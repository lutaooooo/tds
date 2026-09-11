// ============================================================================
// streamNode_rtp.cpp - RTP 流传输层
// 包含：RTP 接收/解析/序列化、缓冲区管理、RTP 分发/转发（含 WebRTC SRTP）、
//       录像（H.264 录制到文件）
// ============================================================================

#include "streamNode.h"
#include "mp4Writer.h"
#include "streamServer.h"
#include "streamSession_webrtc.h"
#include "dtls_transport.h"
#include "srtp_protect.h"
#include <fstream>
#include <cstring>
#include <functional>
#include <cerrno>
#include <logger.h>
#ifndef _WIN32
#include <fcntl.h>
#include <unistd.h>
#endif

// Windows 下将 UTF-8 路径转为宽字符（std::ofstream 的 string 重载使用系统 locale，中文路径需 wchar_t 重载）
#ifdef _WIN32
static std::wstring pathToWide(const std::string& utf8) {
    int len = MultiByteToWideChar(CP_UTF8, 0, utf8.c_str(), -1, nullptr, 0);
    if (len <= 0) return std::wstring();
    std::wstring w(len - 1, L'\0');
    MultiByteToWideChar(CP_UTF8, 0, utf8.c_str(), -1, &w[0], len);
    return w;
}
#endif

// ============================================================================
// RTP 缓冲区管理
// ============================================================================

int StreamNode::getBufferedSeconds()
{
    // 计算当前 rtp_buffer_ 中的数据覆盖的大致秒数
    std::lock_guard<std::mutex> lock(queue_mutex_);

    if (rtp_buffer_.empty()) return 0;

    // 以最早包和最新包的 RTP timestamp 差值为基准计算（无符号，支持回绕）
    uint32_t newest_ts = rtp_buffer_.back()->timestamp;
    uint32_t oldest_ts = rtp_buffer_.front()->timestamp;
    uint32_t diff = newest_ts - oldest_ts; // 无符号差值，处理 32 位回绕

    // 获取时钟频率（ticks per second），RTCP/SDP 中给出，视频常见为 90000
    uint32_t clock = (clock_rate_ > 0) ? static_cast<uint32_t>(clock_rate_) : 90000u;
    if (clock == 0) clock = 90000u;

    // 整数秒（截断子秒）。如果存在刻度差但小于1秒，返回1以提示非空缓冲
    int seconds = static_cast<int>(diff / clock);
    if (diff > 0 && seconds == 0) seconds = 1;
    return seconds;
}

void StreamNode::addToRtpBuffer(std::shared_ptr<RTPPacket> pPkt)
{
    // 校验输入
    if (!pPkt) return;

    // 使用共享指针直接保存引用，无需深拷贝对象。调用者共享同一份数据，
    // 引用计数自动管理生命周期，可安全地在多个消费者间传递。
    std::lock_guard<std::mutex> lock(queue_mutex_);
    rtp_buffer_.push_back(pPkt);

    // 根据 rtp_buffer_max_seconds_ 修剪缓冲区，尽量保持约定秒数的媒体数据。
    if (rtp_buffer_max_seconds_ > 0 && !rtp_buffer_.empty()) {
        uint32_t newest_ts = rtp_buffer_.back()->timestamp;

        // 获取时钟频率（每秒刻度数），若 SDP 未提供则默认使用常见的视频值 90000Hz。
        uint32_t clock = (clock_rate_ > 0) ?
            static_cast<uint32_t>(clock_rate_) : 90000u;
        if (clock == 0) clock = 90000u;

        // 当最旧包到最新包的时间差超过配置的秒数窗口时，逐个删除最旧包。
        while (!rtp_buffer_.empty()) {
            auto oldest = rtp_buffer_.front();
            uint32_t oldest_ts = oldest->timestamp;

            // 无符号相减可以按模 2^32 处理 timestamp 回绕情况。
            uint32_t diff = newest_ts - oldest_ts;

            // 将刻度差转换为整秒（会截断小数部分）。
            uint32_t seconds = diff / clock;

            if (seconds > static_cast<uint32_t>(rtp_buffer_max_seconds_)) {
                // 包已超出时间窗口 -> 从缓冲中移除。
                rtp_buffer_.erase(rtp_buffer_.begin());
            }
            else {
                // 当前最旧包在窗口内，停止修剪。
                break;
            }
        }
    }

    // 额外的保护：强制限制缓冲包数量到 max_queue_size_，以防 timestamp
    // 逻辑失效或时钟信息错误导致内存无限增长。
    while (rtp_buffer_.size() > max_queue_size_) {
        rtp_buffer_.erase(rtp_buffer_.begin());
    }
}

// H.265 随机访问点 NAL 类型（RFC 7798）：BLA(16-18)/IDR(19,20)/CRA(21)。
// 监控编码器常用 CRA 作为 GOP 边界，只认 IDR 会导致关键帧缓存永远不完整、
// 新会话无限等待起播、PLI 兜底失效（黑屏卡死）
static bool isH265RandomAccessNal(uint8_t nalType) {
    return nalType >= NAL_TYPE_H265_BLA_W_LP && nalType <= NAL_TYPE_H265_CRA;
}

bool StreamNode::checkIsIdrNalu(const RTPPacket& packet, const std::string& codec) {
    bool isIdrNalu = false;
    if (packet.payload.empty()) {
        return isIdrNalu;
    }

    // H.265/HEVC：2 字节 NAL header，nal_unit_type = (payload[0] >> 1) & 0x3F
    bool isH265 = (codec == "H265" || codec == "HEVC");
    if (isH265) {
        if (packet.payload.size() < 2) {
            return isIdrNalu;
        }
        uint8_t nalType = (packet.payload[0] >> 1) & 0x3F;
        if (isH265RandomAccessNal(nalType)) {
            isIdrNalu = true;
        }
        else if (nalType == NAL_TYPE_H265_FU && packet.payload.size() > 2) {
            // H.265 FU: [FU indicator(2B)][FU header(1B)]，FU header 低 6 位是 NAL type
            uint8_t fuNalType = packet.payload[2] & 0x3F;
            if (isH265RandomAccessNal(fuNalType)) {
                isIdrNalu = true;
            }
        }
        else if (nalType == NAL_TYPE_H265_AP && packet.payload.size() > 3) {
            // H.265 AP: [AP header(2B)][NALU1 size(2B)][NALU1 data...]...
            // 遍历所有子 NAL：关键帧前常聚合 [VPS,SPS,PPS,IDR]，只查第一个会漏检 IDR
            size_t off = 2;
            while (off + 2 <= packet.payload.size()) {
                uint16_t L = (uint16_t(packet.payload[off]) << 8) | packet.payload[off + 1];
                off += 2;
                if (L == 0 || off + L > packet.payload.size()) break;
                uint8_t subNalType = (packet.payload[off] >> 1) & 0x3F;
                if (isH265RandomAccessNal(subNalType)) {
                    isIdrNalu = true;
                    break;
                }
                off += L;
            }
        }
    }
    else {
        // H.264：1 字节 NAL header，type = payload[0] & 0x1F
        uint8_t nalHeader = packet.payload[0];
        uint8_t nalType = nalHeader & 0x1F;
        if (nalType == NAL_TYPE_IDR) {
            isIdrNalu = true;
        }
        else if (nalType == NAL_TYPE_FU_A && packet.payload.size() > 1) {
            // FU-A: 第二个字节是 FU header，其中低 5 位是 NAL type
            // FU-A: 单个nalu拆多个rtp packet
            uint8_t fuHeader = packet.payload[1];
            uint8_t fuNalType = fuHeader & 0x1F;
            if (fuNalType == NAL_TYPE_IDR) {
                isIdrNalu = true;
            }
        }
        else if (nalType == NAL_TYPE_STAP_A && packet.payload.size() > 3) {
            // STAP-A: [NAL header(1B)][NALU1 size(2B)][NALU1 data...]...
            // 遍历所有子 NAL：相机首帧常用 STAP-A 聚合 [SPS,PPS,IDR]，
            // 只查第一个子 NAL 会漏检 IDR，导致关键帧缓存缺失
            size_t off = 1;
            while (off + 2 <= packet.payload.size()) {
                uint16_t L = (uint16_t(packet.payload[off]) << 8) | packet.payload[off + 1];
                off += 2;
                if (L == 0 || off + L > packet.payload.size()) break;
                if ((packet.payload[off] & 0x1F) == NAL_TYPE_IDR) {
                    isIdrNalu = true;
                    break;
                }
                off += L;
            }
        }
    }
    return isIdrNalu;
}

// ============================================================================
// RTP 分发与转发
// ============================================================================

void StreamNode::sendRTPPacketToClients(const RTPPacket& packet) {
    if (packet.payload.empty())
        return;

    std::vector<std::shared_ptr<STREAM_SESSION>> playClients;
    session_list_client_pull_mutex_.lock();
    playClients = session_list_client_pull_;
    session_list_client_pull_mutex_.unlock();

	// rtsp客户端发送路径：遍历所有拉流客户端，按其传输模式（UDP/TCP）发送 RTP 数据
    for (size_t i = 0; i < playClients.size(); i++) {
        auto& sp = playClients[i];
        if (!sp) continue;
        STREAM_SESSION& client = *sp;
        // WebRTC 客户端走 SRTP 路径，此处跳过明文发送
        if (client.is_webrtc) continue;
        if (client.transport_mode == TransportMode::UDP) {
            // UDP推流（RTSP 明文）
            if (client.sendUDPData(packet.data.data(), packet.data.size())) {
                std::lock_guard<std::mutex> lock(stats_mutex_);
                stats_.bytes_forwarded += packet.data.size();
                stats_.frames_forwarded++;
            }
            else {
                std::lock_guard<std::mutex> lock(stats_mutex_);
                stats_.errors++;
            }
        }
        else if (client.transport_mode == TransportMode::TCP) {
            // TCP interleaved 发送：$channel length data 格式
            if (client.tcp_socket != kInvalidSocket && client.interleaved_rtp >= 0) {
                uint8_t header[4];
                header[0] = 0x24;  // $ magic byte
                header[1] = (uint8_t)(client.interleaved_rtp & 0xFF);
                header[2] = (uint8_t)((packet.data.size() >> 8) & 0xFF);
                header[3] = (uint8_t)(packet.data.size() & 0xFF);

#ifdef _WIN32
                int sent = ::send(client.tcp_socket, (const char*)header, 4, 0);
                if (sent == 4) {
                    sent = ::send(client.tcp_socket, (const char*)packet.data.data(),
                        (int)packet.data.size(), 0);
                }
#else
                int sent = ::send(client.tcp_socket, header, 4, MSG_NOSIGNAL);
                if (sent == 4) {
                    sent = ::send(client.tcp_socket, packet.data.data(), packet.data.size(), MSG_NOSIGNAL);
                }
#endif
                if (sent == (int)packet.data.size()) {
                    std::lock_guard<std::mutex> lock(stats_mutex_);
                    stats_.bytes_forwarded += packet.data.size();
                    stats_.frames_forwarded++;
                }
            }
        }
    }

    // === WebRTC SRTP 发送路径 ===
    // 遍历所有 client_sessions_，对 DTLS+SRTP 已完成的会话通过 SRTP 加密后发送视频
    for (auto& session : playClients) {
        if (!session || !session->is_webrtc) continue;
        // state: streaming=SRTP激活
        if (session->state_ != SESSION_STATE::SESSION_STREAMING) continue;

        // 按会话 codec 解析 NAL 类型：
        // H.264: 1 字节 NAL header, type = payload[0] & 0x1F
        // H.265: 2 字节 NAL header, type = (payload[0] >> 1) & 0x3F
        bool isH265 = (session->codec == "H265" || session->codec == "HEVC");
        uint8_t nalType = isH265
            ? ((packet.payload.size() >= 2) ? ((packet.payload[0] >> 1) & 0x3F) : 0)
            : (packet.payload[0] & 0x1F);

        // 通过 SessionDtlsState 正确访问 DTLS 和 SRTP 上下文
        // dtls_transport_ 为 shared_ptr（由 ICE 线程管理），原子加载快照后持有引用，
        // 避免 ICE 线程释放后发送线程解引用产生 Use-After-Free
        std::shared_ptr<SessionDtlsState> dtlsState_shared = std::atomic_load(&session->dtls_transport_);
        SessionDtlsState* dtlsState = dtlsState_shared.get();
        if (!dtlsState || !dtlsState->srtp_ready) continue;
        if (!dtlsState->dtls.isPeerSet()) continue;

        DtlsTransport& dtls = dtlsState->dtls;
        SrptProtect::Context& srtpCtx = dtlsState->srtp_ctx;

        // 从源流动态缓存参数集（当相机 SDP 不含 sprop 参数时，
        // 后续的 IDR 前插入和首次发送逻辑依赖缓存的参数集）
        // H.264: SPS/PPS 可能以 Single NAL、STAP-A 或 FU-A 格式到达
        // H.265: VPS/SPS/PPS 可能以 Single NAL、AP 或 FU 格式到达（RFC 7798）
        if (isH265) {
            if (nalType == NAL_TYPE_H265_VPS) {
                session->vps = packet.payload;
            } else if (nalType == NAL_TYPE_H265_SPS) {
                session->sps = packet.payload;
            } else if (nalType == NAL_TYPE_H265_PPS) {
                session->pps = packet.payload;
            } else if (nalType == NAL_TYPE_H265_AP && packet.payload.size() > 3) {
                // AP: [AP header(2B)] [NALU1 size(2B)] [NALU1 data] ...
                size_t off = 2;
                while (off + 2 <= packet.payload.size()) {
                    uint16_t L = (packet.payload[off] << 8) | packet.payload[off + 1];
                    off += 2;
                    if (L == 0 || off + L > packet.payload.size()) break;
                    uint8_t subType = (packet.payload[off] >> 1) & 0x3F;
                    if (subType == NAL_TYPE_H265_VPS) {
                        session->vps = std::vector<uint8_t>(
                            packet.payload.begin() + off,
                            packet.payload.begin() + off + L);
                    } else if (subType == NAL_TYPE_H265_SPS) {
                        session->sps = std::vector<uint8_t>(
                            packet.payload.begin() + off,
                            packet.payload.begin() + off + L);
                    } else if (subType == NAL_TYPE_H265_PPS) {
                        session->pps = std::vector<uint8_t>(
                            packet.payload.begin() + off,
                            packet.payload.begin() + off + L);
                    }
                    off += L;
                }
            } else if (nalType == NAL_TYPE_H265_FU && packet.payload.size() > 2) {
                // FU 分片：检查是否包含参数集（虽然参数集通常很小，不会分片，但为了完整性）
                uint8_t fuNalType = packet.payload[2] & 0x3F;
                if (fuNalType == NAL_TYPE_H265_VPS || fuNalType == NAL_TYPE_H265_SPS || fuNalType == NAL_TYPE_H265_PPS) {
                    // 注意：参数集的 FU 分片需要完整重组才能使用，这里暂时不处理
                    // 因为参数集通常很小，不会被分片
                }
            }
        } else {
            if (nalType == NAL_TYPE_SPS) {
                session->sps = packet.payload;
            } else if (nalType == NAL_TYPE_PPS) {
                session->pps = packet.payload;
            } else if (nalType == NAL_TYPE_STAP_A && packet.payload.size() > 3) {
                // STAP-A: [STAP-A header(1B)] [NALU1 size(2B)] [NALU1 data] ...
                size_t off = 1;
                while (off + 2 <= packet.payload.size()) {
                    uint16_t L = (packet.payload[off] << 8) | packet.payload[off + 1];
                    off += 2;
                    if (L == 0 || off + L > packet.payload.size()) break;
                    uint8_t subType = packet.payload[off] & 0x1F;
                    if (subType == NAL_TYPE_SPS) {
                        session->sps = std::vector<uint8_t>(
                            packet.payload.begin() + off,
                            packet.payload.begin() + off + L);
                    } else if (subType == NAL_TYPE_PPS) {
                        session->pps = std::vector<uint8_t>(
                            packet.payload.begin() + off,
                            packet.payload.begin() + off + L);
                    }
                    off += L;
                }
            } else if (nalType == NAL_TYPE_FU_A && packet.payload.size() > 1) {
                // FU-A 极少用于 SPS/PPS（SPS/PPS 通常很小无需分片），暂不处理
            }
        }

        // 初始化 per-session 序列号（以原始流第一个包的 seq 为基准）
        if (!dtlsState->seq_inited) {
            dtlsState->local_seq = packet.sequence_number;
            dtlsState->seq_inited = true;
        }

        auto now_steady = std::chrono::steady_clock::now();

        // 确定本会话使用的 SSRC，必须与 SDP Answer 中声明的 a=ssrc: 一致
        uint32_t sessionSsrc = session->video_ssrc ? session->video_ssrc : 1;

        // 安全 MTU 上限：单个 RTP 负载（不含 12B RTP 头与 SRTP 认证标签）最大字节数。
        // 取 1180 可保证叠加 SRTP 标签后在标准/隧道 MTU 下均不超 1500，避免弱网大包被丢弃。
        const size_t kMaxRtpPayload = 1180;

        // 发送门控诊断：每 5 秒汇总一次（进包/转发/各门控丢弃/关键帧缓存状态）
        dtlsState->dbg_pkts++;
        if (packet.isIdrNalu) dtlsState->dbg_idr++;
        {
            auto now2 = std::chrono::steady_clock::now();
            if (dtlsState->dbg_last_log.time_since_epoch().count() == 0)
                dtlsState->dbg_last_log = now2;
            if (std::chrono::duration<double>(now2 - dtlsState->dbg_last_log).count() >= 5.0) {
                bool kfC = false; size_t kfN = 0;
                {
                    std::lock_guard<std::mutex> lk(keyframe_cache_mutex_);
                    kfC = keyframe_cache_.complete;
                    kfN = keyframe_cache_.pkts.size();
                }
                LOG("[WebRTC][diag] fd=%d pkts=%llu fwd=%llu dropNoKey=%llu dropMid=%llu idr=%llu "
                    "firstSend=%d kfComplete=%d kfN=%zu vps=%d sps=%d pps=%d",
                    (int)session->rtp_socket,
                    (unsigned long long)dtlsState->dbg_pkts, (unsigned long long)dtlsState->dbg_fwd,
                    (unsigned long long)dtlsState->dbg_drop_nokey, (unsigned long long)dtlsState->dbg_drop_mid,
                    (unsigned long long)dtlsState->dbg_idr,
                    (int)session->is_first_send_, (int)kfC, kfN,
                    (int)!session->vps.empty(), (int)!session->sps.empty(), (int)!session->pps.empty());
                dtlsState->dbg_last_log = now2;
                dtlsState->dbg_pkts = 0; dtlsState->dbg_fwd = 0;
                dtlsState->dbg_drop_nokey = 0; dtlsState->dbg_drop_mid = 0;
                dtlsState->dbg_idr = 0;
            }
        }

        // 关键帧最大发送间隔(ms)：超过则置位待重发标志（在下一个帧边界执行重发），
        // 作为"源流长时间无关键帧通过"的自愈兜底，不依赖浏览器是否发送 PLI。
        // 必须 >> 正常 GOP：阈值小于 GOP 的健康流会被周期性注入冗余关键帧
        // （旧值 2000ms 在 GOP>2s 的流上正是"画面每 2 秒跳变一次"的来源之一）
        const int kMaxIdrGapMs = 10000;

        // 发送一个已构建好的 RTP 包（rtp[0..1] 含 V/PT/marker，rtp[4..11] 含 ts/ssrc 已填）：
        // 在此填入 per-session 序列号、SRTP 加密并发送，随后序列号自增。
        auto sendBuiltRtp = [&](std::vector<uint8_t>& rtp) {
            uint16_t sentSeq = dtlsState->local_seq;
            rtp[2] = (dtlsState->local_seq >> 8) & 0xFF;
            rtp[3] = dtlsState->local_seq & 0xFF;
            dtlsState->local_seq++;
            dtlsState->dbg_fwd++;
            auto srtpPkt = SrptProtect::protect(srtpCtx, rtp);
            if (srtpPkt.empty()) return;

            // 缓存已加密的 SRTP 包，供收到 NACK 时原样重传（修复弱网单包丢失导致的花屏）
            {
                std::lock_guard<std::mutex> lk(dtlsState->rtx_mutex_);
                RtxCachedPacket& slot =
                    dtlsState->rtx_buf_[sentSeq % SessionDtlsState::kRtxBufSize];
                slot.seq = sentSeq;
                slot.valid = true;
                slot.data = srtpPkt;
            }

            const struct sockaddr_in& peerAddr = dtls.getPeerAddr();
            int sent = sendto(session->rtp_socket,
                (const char*)srtpPkt.data(), (int)srtpPkt.size(), 0,
                (const struct sockaddr*)&peerAddr, sizeof(peerAddr));
            if (sent < 0) {
#ifdef _WIN32
                int err = WSAGetLastError();
                LOG("[SRTP] sendto FAILED, err=%d, pkt=%zu", err, srtpPkt.size());
#else
                LOG("[SRTP] sendto FAILED, errno=%d, pkt=%zu", errno, srtpPkt.size());
#endif
            }
            if (sent > 0) {
                std::lock_guard<std::mutex> lock(stats_mutex_);
                stats_.bytes_forwarded += srtpPkt.size();
                stats_.frames_forwarded++;
            }
        };

        // 把一个 NALU（含其 NAL 头字节）重新打包成一个或多个 RTP 包发送。
        // H.264：Single NAL（≤kMaxRtpPayload）直接发送，更大则用 FU-A 切分；
        //        STAP-A 聚合包先拆成单 NAL 逐发；相机已 FU-A 分片但单片仍过大的，按片再切小。
        // H.265：Single NAL（≤kMaxRtpPayload）直接发送，更大则用 FU（2B indicator + 1B FU header）切分；
        //        AP 聚合包先拆成单 NAL 逐发；相机已 FU 分片但单片仍过大的，按片再切小。
        std::function<void(const std::vector<uint8_t>&, uint32_t, bool)> sendNalu =
            [&](const std::vector<uint8_t>& nalu, uint32_t ts, bool marker) {
            if (nalu.empty()) return;

            if (isH265) {
                if (nalu.size() < 2) return;
                uint8_t nt = (nalu[0] >> 1) & 0x3F;

                // H.265 AP：拆成多个单 NAL 逐发（marker 仅落在最后一个子 NALU 上）
                if (nt == NAL_TYPE_H265_AP) {
                    size_t off = 2;
                    while (off + 2 <= nalu.size()) {
                        uint16_t L = (uint16_t(nalu[off]) << 8) | uint16_t(nalu[off + 1]);
                        off += 2;
                        if (L == 0 || off + L > nalu.size()) break;
                        bool isLast = (off + L >= nalu.size());
                        std::vector<uint8_t> sub(nalu.begin() + off, nalu.begin() + off + L);
                        sendNalu(sub, ts, marker && isLast);
                        off += L;
                    }
                    return;
                }

                // 相机已 FU 分片：单 RTP 包内负载(含 3B FU 头)未超上限则原样重映射发送；
                // 仍过大（弱网隧道场景）时按片再切成更小的 FU。
                if (nt == NAL_TYPE_H265_FU) {
                    if (nalu.size() <= kMaxRtpPayload) {
                        std::vector<uint8_t> rtp(12 + nalu.size());
                        rtp[0] = 0x80;
                        rtp[1] = (marker ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                        rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                        rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                        rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                        rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                        memcpy(&rtp[12], nalu.data(), nalu.size());
                        sendBuiltRtp(rtp);
                    }
                    else {
                        uint8_t fuType = nalu[2] & 0x3F;
                        bool camS = (nalu[2] & 0x80) != 0;
                        bool camE = (nalu[2] & 0x40) != 0;
                        size_t dataLen = nalu.size() - 3;
                        size_t chunkMax = kMaxRtpPayload - 3;
                        size_t pos = 0;
                        while (pos < dataLen) {
                            size_t frag = (dataLen - pos > chunkMax) ? chunkMax : (dataLen - pos);
                            bool isFirst = (pos == 0) && camS;
                            bool isLast = (pos + frag >= dataLen) && camE;
                            std::vector<uint8_t> rtp(12 + 3 + frag);
                            rtp[0] = 0x80;
                            rtp[1] = ((isLast && marker) ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                            rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                            rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                            rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                            rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                            rtp[12] = nalu[0]; rtp[13] = nalu[1];  // FU indicator 原样（2B）
                            rtp[14] = (uint8_t)(fuType | (isFirst ? 0x80 : 0) | (isLast ? 0x40 : 0));
                            memcpy(&rtp[15], &nalu[3 + pos], frag);
                            sendBuiltRtp(rtp);
                            pos += frag;
                        }
                    }
                    return;
                }

                // Single NAL（或未识别类型）：过大则 FU 切分，否则直接发送
                if (nalu.size() <= kMaxRtpPayload) {
                    std::vector<uint8_t> rtp(12 + nalu.size());
                    rtp[0] = 0x80;
                    rtp[1] = (marker ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                    rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                    rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                    rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                    rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                    memcpy(&rtp[12], nalu.data(), nalu.size());
                    sendBuiltRtp(rtp);
                }
                else {
                    uint8_t nalType = nt;
                    // H.265 FU indicator (2 bytes): [F(1)][Type(6)][LayerId_high(1)] [LayerId_low(5)][TID(3)]
                    // Type = 49 (FU), F = forbidden bit from original NAL, LayerId = 0, TID = 1
                    uint8_t fuIndicator0 = (nalu[0] & 0x81) | (NAL_TYPE_H265_FU << 1);  // F bit + Type=49 + LayerId_high
                    uint8_t fuIndicator1 = (nalu[1] & 0xF8) | 0x01;  // LayerId_low=0 + TID=1
                    size_t chunkMax = kMaxRtpPayload - 3;
                    size_t offset = 2;
                    bool first = true;
                    while (offset < nalu.size()) {
                        size_t remain = nalu.size() - offset;
                        size_t frag = (remain > chunkMax) ? chunkMax : remain;
                        bool isLast = (offset + frag >= nalu.size());
                        std::vector<uint8_t> rtp(12 + 3 + frag);
                        rtp[0] = 0x80;
                        rtp[1] = ((isLast && marker) ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                        rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                        rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                        rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                        rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                        rtp[12] = fuIndicator0; rtp[13] = fuIndicator1;  // FU indicator（2B）
                        rtp[14] = (uint8_t)(nalType | (first ? 0x80 : 0) | (isLast ? 0x40 : 0));
                        memcpy(&rtp[15], &nalu[offset], frag);
                        sendBuiltRtp(rtp);
                        offset += frag;
                        first = false;
                    }
                }
                return;
            }

            // H.264 路径
            uint8_t nt = nalu[0] & 0x1F;

            // STAP-A：拆成多个单 NAL 逐发（marker 仅落在最后一个子 NALU 上）
            if (nt == NAL_TYPE_STAP_A) {
                size_t off = 1;
                while (off + 2 <= nalu.size()) {
                    uint16_t L = (uint16_t(nalu[off]) << 8) | uint16_t(nalu[off + 1]);
                    off += 2;
                    if (L == 0 || off + L > nalu.size()) break;
                    bool isLast = (off + L >= nalu.size());
                    std::vector<uint8_t> sub(nalu.begin() + off, nalu.begin() + off + L);
                    sendNalu(sub, ts, marker && isLast);
                    off += L;
                }
                return;
            }

            // 相机已 FU-A 分片：单 RTP 包内负载(含 2B FU 头)未超上限则原样重映射发送；
            // 仍过大（弱网隧道场景）时按片再切成更小的 FU-A。
            if (nt == NAL_TYPE_FU_A) {
                if (nalu.size() <= kMaxRtpPayload) {
                    std::vector<uint8_t> rtp(12 + nalu.size());
                    rtp[0] = 0x80;
                    rtp[1] = (marker ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                    rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                    rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                    rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                    rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                    memcpy(&rtp[12], nalu.data(), nalu.size());
                    sendBuiltRtp(rtp);
                }
                else {
                    uint8_t nri = nalu[0] & 0x60;
                    uint8_t fuType = nalu[1] & 0x1F;
                    bool camS = (nalu[1] & 0x80) != 0;
                    bool camE = (nalu[1] & 0x40) != 0;
                    size_t dataLen = nalu.size() - 2;
                    size_t chunkMax = kMaxRtpPayload - 2;
                    size_t pos = 0;
                    while (pos < dataLen) {
                        size_t frag = (dataLen - pos > chunkMax) ? chunkMax : (dataLen - pos);
                        bool isFirst = (pos == 0) && camS;
                        bool isLast = (pos + frag >= dataLen) && camE;
                        std::vector<uint8_t> rtp(12 + 2 + frag);
                        rtp[0] = 0x80;
                        rtp[1] = ((isLast && marker) ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                        rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                        rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                        rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                        rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                        rtp[12] = 0x1C | nri;   // FU indicator, type=28
                        rtp[13] = (uint8_t)(fuType | (isFirst ? 0x80 : 0) | (isLast ? 0x40 : 0));
                        memcpy(&rtp[14], &nalu[2 + pos], frag);
                        sendBuiltRtp(rtp);
                        pos += frag;
                    }
                }
                return;
            }

            // Single NAL（或未识别类型）：过大则 FU-A 切分，否则直接发送
            if (nalu.size() <= kMaxRtpPayload) {
                std::vector<uint8_t> rtp(12 + nalu.size());
                rtp[0] = 0x80;
                rtp[1] = (marker ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                memcpy(&rtp[12], nalu.data(), nalu.size());
                sendBuiltRtp(rtp);
            }
            else {
                uint8_t nri = nalu[0] & 0x60;
                uint8_t nalType = nalu[0] & 0x1F;
                size_t chunkMax = kMaxRtpPayload - 2;
                size_t offset = 1;
                bool first = true;
                while (offset < nalu.size()) {
                    size_t remain = nalu.size() - offset;
                    size_t frag = (remain > chunkMax) ? chunkMax : remain;
                    bool isLast = (offset + frag >= nalu.size());
                    std::vector<uint8_t> rtp(12 + 2 + frag);
                    rtp[0] = 0x80;
                    rtp[1] = ((isLast && marker) ? 0x80 : 0x00) | (session->payload_type & 0x7F);
                    rtp[4] = (ts >> 24) & 0xFF; rtp[5] = (ts >> 16) & 0xFF;
                    rtp[6] = (ts >> 8) & 0xFF;  rtp[7] = ts & 0xFF;
                    rtp[8] = (sessionSsrc >> 24) & 0xFF; rtp[9] = (sessionSsrc >> 16) & 0xFF;
                    rtp[10] = (sessionSsrc >> 8) & 0xFF;  rtp[11] = sessionSsrc & 0xFF;
                    rtp[12] = 0x1C | nri;   // FU indicator, type=28
                    rtp[13] = (uint8_t)(nalType | (first ? 0x80 : 0) | (isLast ? 0x40 : 0));
                    memcpy(&rtp[14], &nalu[offset], frag);
                    sendBuiltRtp(rtp);
                    offset += frag;
                    first = false;
                }
            }
        };

        // 发送单个 NAL（参数集等小包），marker=0
        auto sendSingleNalRtp = [&](const std::vector<uint8_t>& nal, uint32_t ts) {
            sendNalu(nal, ts, false);
        };

        // 在 IDR 帧前发送参数集（H.264: SPS/PPS；H.265: VPS/SPS/PPS）。
        // 依赖带内参数集初始化解码器的浏览器，IDR 前缺失参数集会直接花屏
        auto sendParamSetsBeforeIdr = [&](uint32_t ts) {
            if (isH265) {
                if (!session->vps.empty()) {
                    sendSingleNalRtp(session->vps, ts);
                } else {
                    LOG("[WebRTC] WARNING: H265 IDR frame without VPS");
                }
            }
            if (!session->sps.empty()) sendSingleNalRtp(session->sps, ts);
            if (!session->pps.empty()) sendSingleNalRtp(session->pps, ts);
        };

        // 重发缓存的关键帧（H.264: SPS+PPS+IDR 分片；H.265: VPS+SPS+PPS+IDR 分片）。
        // 缓存的是相机原始 RTP 包（含 12B 头），
        // 需解析出 NALU 后按安全 MTU 重新分片发送，避免大 IDR 包在弱网被 MTU 丢弃。
        auto resendKeyframe = [&]() {
            // 锁内拷贝出缓存快照，锁外发送：keyframe_cache_ 由 onRecvOriginRtpPkt
            // （拉流/推流线程）无锁并发维护，这里必须与写入侧互斥
            std::vector<std::vector<uint8_t>> kfPkts;
            bool kfComplete = false;
            {
                std::lock_guard<std::mutex> lk(keyframe_cache_mutex_);
                kfPkts = keyframe_cache_.pkts;
                kfComplete = keyframe_cache_.complete;
            }
            // 缓存为空或不完整（IDR 分片有缺失）时不重发：
            // 重发不完整的关键帧会让浏览器组帧失败继续花屏，宁可等源流下一帧 IDR
            if (kfPkts.empty() || !kfComplete) return;
            
            // 对于 H.265，必须先发送参数集（VPS/SPS/PPS），否则解码器无法初始化
            if (isH265) {
                if (!session->vps.empty()) {
                    sendSingleNalRtp(session->vps, packet.timestamp);
                } else {
                    // 如果没有 VPS，尝试从关键帧缓存中提取
                    for (auto& kfData : kfPkts) {
                        RTPPacket kfPkt;
                        if (!kfPkt.parse(kfData.data(), kfData.size())) continue;
                        uint8_t kfNalType = (kfPkt.payload.size() >= 2) ? ((kfPkt.payload[0] >> 1) & 0x3F) : 0;
                        if (kfNalType == NAL_TYPE_H265_VPS) {
                            session->vps = kfPkt.payload;
                            sendSingleNalRtp(session->vps, packet.timestamp);
                            break;
                        }
                    }
                }
            }
            
            // 发送 SPS/PPS（H.264 和 H.265 都需要）
            if (!session->sps.empty()) {
                sendSingleNalRtp(session->sps, packet.timestamp);
            } else {
                // 如果没有 SPS，尝试从关键帧缓存中提取
                for (auto& kfData : kfPkts) {
                    RTPPacket kfPkt;
                    if (!kfPkt.parse(kfData.data(), kfData.size())) continue;
                    uint8_t kfNalType;
                    if (isH265) {
                        kfNalType = (kfPkt.payload.size() >= 2) ? ((kfPkt.payload[0] >> 1) & 0x3F) : 0;
                    } else {
                        kfNalType = (kfPkt.payload.size() >= 1) ? (kfPkt.payload[0] & 0x1F) : 0;
                    }
                    if ((isH265 && kfNalType == NAL_TYPE_H265_SPS) || (!isH265 && kfNalType == NAL_TYPE_SPS)) {
                        session->sps = kfPkt.payload;
                        sendSingleNalRtp(session->sps, packet.timestamp);
                        break;
                    }
                }
            }
            
            if (!session->pps.empty()) {
                sendSingleNalRtp(session->pps, packet.timestamp);
            } else {
                // 如果没有 PPS，尝试从关键帧缓存中提取
                for (auto& kfData : kfPkts) {
                    RTPPacket kfPkt;
                    if (!kfPkt.parse(kfData.data(), kfData.size())) continue;
                    uint8_t kfNalType;
                    if (isH265) {
                        kfNalType = (kfPkt.payload.size() >= 2) ? ((kfPkt.payload[0] >> 1) & 0x3F) : 0;
                    } else {
                        kfNalType = (kfPkt.payload.size() >= 1) ? (kfPkt.payload[0] & 0x1F) : 0;
                    }
                    if ((isH265 && kfNalType == NAL_TYPE_H265_PPS) || (!isH265 && kfNalType == NAL_TYPE_PPS)) {
                        session->pps = kfPkt.payload;
                        sendSingleNalRtp(session->pps, packet.timestamp);
                        break;
                    }
                }
            }
            
            RTPPacket kfPkt;
            for (auto& kfData : kfPkts) {
                if (!kfPkt.parse(kfData.data(), kfData.size())) continue;
                // 使用缓存包自身的时间戳重发：用当前包 ts 会导致同 ts 双帧，
                // 浏览器组帧/解码错乱（偶发花屏）
                sendNalu(kfPkt.payload, kfPkt.timestamp, kfPkt.marker);
            }
        };

        // 响应浏览器 PLI/FIR：消费请求但【不在此处立即重发】——此刻正处理的包
        // 位于某个活帧中间，把整个缓存关键帧爆发（几十个包）插进来会割裂该帧：
        // 前半段失去 E/marker、后半段失去 S 起始，浏览器 PacketBuffer 组帧链
        // 被阻塞，实测表现为画面只有重发的关键帧在跳变、其余时间完全冻结。
        // 改为置 resend_pending_，在下一个活帧的帧边界统一执行（帧对齐插入）。
        // 节流：距上次关键帧发送不足 300ms 时保留请求标志稍后消费，
        // 避免 PLI 风暴导致关键帧流量暴涨
        if (dtlsState->request_keyframe_resend_) {
            if (now_steady - dtlsState->last_idr_sent_time_ >= std::chrono::milliseconds(300)) {
                dtlsState->request_keyframe_resend_ = false;
                dtlsState->resend_pending_ = true;
            }
        }

        // 帧边界判定：isLastIdrNalu==false 表示本包是某个新帧的第一包
        const bool isNewFrameStart = (packet.isLastIdrNalu == false);
        bool burstSentThisPacket = false;

        // 新会话首次发送：缓存的关键帧（含参数集）必须落在帧边界上。
        // 帧中间到达时丢弃本包（半帧对浏览器组帧无意义），等下一个帧首再起播。
        // 缓存就绪（完整 IDR 已缓存）时在帧首补发关键帧加速出图；
        // 缓存未就绪时丢弃非 IDR 包，避免浏览器在无参考帧时解码花屏
        if (session->is_first_send_) {
            bool kfReady = false;
            {
                std::lock_guard<std::mutex> lk(keyframe_cache_mutex_);
                kfReady = keyframe_cache_.complete && !keyframe_cache_.pkts.empty();
            }
            
            // 对于 H.265，必须确保参数集（VPS/SPS/PPS）已准备好
            bool h265ParamsReady = true;
            if (isH265) {
                h265ParamsReady = !session->vps.empty() && !session->sps.empty() && !session->pps.empty();
                if (!h265ParamsReady) {
                    // 尝试从关键帧缓存中提取参数集
                    if (kfReady) {
                        std::vector<std::vector<uint8_t>> kfPkts;
                        {
                            std::lock_guard<std::mutex> lk(keyframe_cache_mutex_);
                            kfPkts = keyframe_cache_.pkts;
                        }
                        for (auto& kfData : kfPkts) {
                            RTPPacket kfPkt;
                            if (!kfPkt.parse(kfData.data(), kfData.size())) continue;
                            uint8_t kfNalType = (kfPkt.payload.size() >= 2) ? ((kfPkt.payload[0] >> 1) & 0x3F) : 0;
                            if (kfNalType == NAL_TYPE_H265_VPS && session->vps.empty()) {
                                session->vps = kfPkt.payload;
                            } else if (kfNalType == NAL_TYPE_H265_SPS && session->sps.empty()) {
                                session->sps = kfPkt.payload;
                            } else if (kfNalType == NAL_TYPE_H265_PPS && session->pps.empty()) {
                                session->pps = kfPkt.payload;
                            }
                        }
                        h265ParamsReady = !session->vps.empty() && !session->sps.empty() && !session->pps.empty();
                    }
                    
                    // 如果仍然没有参数集，记录警告并继续（可能依赖 SDP 中的 sprop）
                    if (!h265ParamsReady) {
                        LOG("[WebRTC] WARNING: H265 session missing VPS/SPS/PPS, attempting to continue");
                    }
                }
            }
            
            if (!kfReady && !packet.isIdrNalu) {
                dtlsState->dbg_drop_nokey++;
                continue;  // 无参考帧可发，丢弃非关键帧，等下一个 IDR
            }
            if (!isNewFrameStart) {
                dtlsState->dbg_drop_mid++;
                continue;  // 帧中间到达：丢弃本包，等下一个帧边界再首次发送
            }
            session->is_first_send_ = false;
            if (kfReady) {
                resendKeyframe();
                dtlsState->last_idr_sent_time_ = now_steady;
                burstSentThisPacket = true;
                // 本帧首已同步重发过缓存关键帧，撤销可能存在的待重发标记
                dtlsState->resend_pending_ = false;
                LOG("first send: sps/pps + keyframe for session");
            }
            else if (packet.isIdrNalu && packet.isLastIdrNalu == false) {
                // 缓存未就绪、但本包是 live IDR 的帧首：参数集必须补在 IDR 前，
                // 否则首个 IDR 无带内参数集，不认 SDP sprop 的浏览器无法初始化
                // 解码器（实测 Chrome H265 会持续 PLI 拿不到关键帧、零解码）
                sendParamSetsBeforeIdr(packet.timestamp);
                dtlsState->last_idr_sent_time_ = now_steady;
                LOG("first send: params + live keyframe (cache incomplete)");
            }
        }
        else {
            // 主动重发兜底：距上次关键帧发送超过阈值（10s）说明源流长时间
            // 无关键帧通过（弱网丢 IDR / CRA 漏检），置位待帧边界执行。
            // 注意不能太小：GOP 大于阈值的健康流会被周期性插入冗余关键帧，
            // 旧行为（2s）正是"画面每 2 秒跳一次"的直接来源之一
            if (now_steady - dtlsState->last_idr_sent_time_ >= std::chrono::milliseconds(kMaxIdrGapMs)) {
                dtlsState->resend_pending_ = true;
                dtlsState->last_idr_sent_time_ = now_steady;  // 防止逐包重复置位
            }
            // 帧边界执行待重发（含 PLI 请求与兜底）：参数集 + 缓存关键帧
            if (isNewFrameStart && dtlsState->resend_pending_) {
                dtlsState->resend_pending_ = false;
                resendKeyframe();
                dtlsState->last_idr_sent_time_ = now_steady;
                burstSentThisPacket = true;
                // LOG("[WebRTC] keyframe resend at frame boundary");
            }
            // 每个IDR之前发送参数集（H.264: SPS/PPS；H.265: VPS/SPS/PPS），
            // 与重发爆发互斥（爆发内已含参数集）。
            // 注意：last_idr_sent_time_ 刷新在参数集是否为空之前——
            // 相机 RTP 流不带参数集包（仅 SDP sprop 提供）时，IDR 帧到达同样算关键帧已发送，
            // 否则周期重发会在每个 IDR 帧上再叠加一次完整重发（关键帧流量翻倍）
            else if (packet.isIdrNalu && packet.isLastIdrNalu == false && !burstSentThisPacket) {
                sendParamSetsBeforeIdr(packet.timestamp);
                dtlsState->last_idr_sent_time_ = now_steady;
            }
        }

        // 重新分片发送本帧负载（安全 MTU，解决弱网大包被丢弃导致的冻结/花屏）
        sendNalu(packet.payload, packet.timestamp, packet.marker);

    }
}

void StreamNode::forwardRTPPacket(const RTPPacket & packet) {
    // 序列化RTP包
    auto data = packet.serialize();
    
    if (session_relay_push_.transport_mode == TransportMode::UDP) {
        // UDP推流
        if (session_relay_push_.sendUDPData(data.data(), data.size())) {
            std::lock_guard<std::mutex> lock(stats_mutex_);
            stats_.bytes_forwarded += data.size();
            stats_.frames_forwarded++;
        }
        else {
            std::lock_guard<std::mutex> lock(stats_mutex_);
            stats_.errors++;
        }
    }
    else {
        // TCP推流：发送到目标RTSP服务器（通过RTSP控制的连接）
        if (session_relay_push_.conn_ && session_relay_push_.conn_->isConnected()) {
            // RTP over RTSP: 插入 $ (0x24) + channel + length
            int rtp_channel = (session_relay_push_.interleaved_rtp >= 0)
                ? session_relay_push_.interleaved_rtp : 0;
            uint8_t rtpOverTcp[4] = { 0x24, (uint8_t)(rtp_channel & 0xFF), 0x00, 0x00 };
            rtpOverTcp[2] = (data.size() >> 8) & 0xFF;
            rtpOverTcp[3] = data.size() & 0xFF;
            
            std::vector<uint8_t> tcpPacket;
            tcpPacket.insert(tcpPacket.end(), rtpOverTcp, rtpOverTcp + 4);
            tcpPacket.insert(tcpPacket.end(), data.begin(), data.end());
            
            int sent = session_relay_push_.conn_->send(tcpPacket.data(), tcpPacket.size());
            if (sent > 0) {
                session_relay_push_.rtpBytesSended += data.size();
                std::lock_guard<std::mutex> lock(stats_mutex_);
                stats_.bytes_forwarded += data.size();
                stats_.frames_forwarded++;
            }
        }
    }
}

// ============================================================================
// RTP 包解析与序列化
// ============================================================================

bool StreamNode::RTPPacket::parse(const uint8_t * data, size_t size) {
    if (size < 12) return false;

    version = (data[0] >> 6) & 0x03;
    padding = (data[0] >> 5) & 0x01;
    extension = (data[0] >> 4) & 0x01;
    csrc_count = data[0] & 0x0F;
    marker = (data[1] >> 7) & 0x01;
    payload_type = data[1] & 0x7F;

    sequence_number = (data[2] << 8) | data[3];
    timestamp = (data[4] << 24) | (data[5] << 16) | (data[6] << 8) | data[7];
    ssrc = (data[8] << 24) | (data[9] << 16) | (data[10] << 8) | data[11];

    size_t header_size = 12 + (csrc_count * 4);
    if (extension) {
        if (size < header_size + 4) return false;
        uint16_t extension_length = (data[header_size + 2] << 8) | data[header_size + 3];
        header_size += 4 + extension_length * 4;
    }

    if (size <= header_size) return false;

    payload.assign(data + header_size, data + size);
    return true;
}

std::vector<uint8_t> StreamNode::RTPPacket::serialize() const {
    // 未保存 padding 字节/扩展头/CSRC 列表，序列化时不再声称包含它们：
    // 保留标志位但无对应数据会使接收端按 padding/extension 长度解析错乱（花屏）
    std::vector<uint8_t> data(12 + payload.size());

    data[0] = (version << 6);
    data[1] = (marker << 7) | (payload_type & 0x7F);

    data[2] = (sequence_number >> 8) & 0xFF;
    data[3] = sequence_number & 0xFF;

    data[4] = (timestamp >> 24) & 0xFF;
    data[5] = (timestamp >> 16) & 0xFF;
    data[6] = (timestamp >> 8) & 0xFF;
    data[7] = timestamp & 0xFF;

    data[8] = (ssrc >> 24) & 0xFF;
    data[9] = (ssrc >> 16) & 0xFF;
    data[10] = (ssrc >> 8) & 0xFF;
    data[11] = ssrc & 0xFF;

    // 复制负载
    if (!payload.empty()) {
        memcpy(data.data() + 12, payload.data(), payload.size());
    }

    return data;
}

// ============================================================================
// NAL 类型描述
// ============================================================================

std::string getNALTypeDesc(unsigned char nal_type) {
    switch (nal_type) {
    case 0: return "Unspecified (0)";
    case 1: return "Non-IDR slice (Coded slice of a non-IDR picture)";
    case 2: return "Partition A (coded slice data partition A)";
    case 3: return "Partition B (coded slice data partition B)";
    case 4: return "Partition C (coded slice data partition C)";
    case 5: return "IDR slice (Instantaneous Decoding Refresh)";
    case 6: return "SEI (Supplemental enhancement information)";
    case 7: return "SPS (Sequence Parameter Set)";
    case 8: return "PPS (Picture Parameter Set)";
    case 9: return "AUD (Access Unit Delimiter)";
    case 10: return "End of sequence";
    case 11: return "End of stream";
    case 12: return "Filler data";
    case 13: return "Reserved (13)";
    case 14: return "Prefix NALU (SVAC) / Prefix";
    case 15: return "Subset SPS (SVAC)";
    case 16: return "Reserved (16)";
    case 17: return "Reserved (17)";
    case 18: return "Reserved (18)";
    case 19: return "Slice extension";
    case 20: return "Slice extension for 3D";
    case 21: return "Slice extension depth";
    case 22: return "Reserved (22)";
    case 23: return "Reserved (23)";
    case 24: return "STAP-A (Single-time aggregation packet)";
    case 25: return "STAP-B (Single-time aggregation packet, with DON)";
    case 26: return "MTAP16 (Multi-time aggregation packet, 16-bit offsets)";
    case 27: return "MTAP24 (Multi-time aggregation packet, 24-bit offsets)";
    case 28: return "FU-A (Fragmentation Unit A)";
    case 29: return "FU-B (Fragmentation Unit B)";
    case 30: return "Unspecified (30)";
    case 31: return "Unspecified (31)";
    default: {
        return std::string("Unknown/Unspecified NAL type: ") + std::to_string((int)nal_type);
    }
    }
}

// ============================================================================
// 录像（H.264 写入文件）
// ============================================================================

// 将 RTP 包推入录像队列（由独立 I/O 线程异步写盘，与实时收包线程解耦）
void StreamNode::recordRTPPacket(std::shared_ptr<RTPPacket> packet) {
    if (!packet) return;  // 防御：上游意外传入 null 时直接丢弃，避免空指针进入录像队列
    std::lock_guard<std::recursive_mutex> lock(rec_mutex_);
    if (!rec_ctrl_.recording) return;  // 双重检查：锁获取期间 recording 可能已被 stopRecord 置 false
    if (rec_ctrl_.firstWrite && !rec_ctrl_.preRecordingDone) {
        // 首写时从 rtp_buffer_ 一次性回溯预录数据。
        // 回溯起点取「preSeconds 时间窗最旧包」与「最近一个关键帧起始包」中更旧者：
        // 录像文件必须以关键帧开头（writeNALtoFile 的 firstWrite 门控会丢弃关键帧前
        // 的一切），否则录制窗口内不含关键帧时（H265 长 GOP 相机 + 录制时长短）
        // 一个 NAL 都写不出，产出 0 字节文件。
        // 关键帧比时间窗更旧时按时间窗回溯（维持长预录语义，多余非关键帧由门控丢弃）。
        std::vector<std::shared_ptr<RTPPacket>> pre_packets;
        {
            std::lock_guard<std::mutex> lock(queue_mutex_);
            uint32_t _clock = (clock_rate_ > 0) ? static_cast<uint32_t>(clock_rate_) : 90000u;
            uint64_t window = static_cast<uint64_t>(rec_ctrl_.preSeconds) * _clock;
            const size_t bufSize = rtp_buffer_.size();

            // 时间窗最旧包的正向下标（新→旧扫描中最后一个仍落在窗口内的包）
            size_t winBegin = bufSize;
            for (size_t i = bufSize; i > 0; i--) {
                auto& p = rtp_buffer_[i - 1];
                if (!p) continue;
                if (packet->timestamp - p->timestamp <= window) winBegin = i - 1;
                else break;
            }

            // 最近一个关键帧（含分片帧）起始包的正向下标：
            // 新→旧扫描先命中关键帧任意分片，再走到帧头（isIdrNalu 变假或时间戳变化）
            size_t keyBegin = bufSize;
            bool haveKey = false;
            uint32_t keyTs = 0;
            for (size_t i = bufSize; i > 0; i--) {
                auto& p = rtp_buffer_[i - 1];
                if (!p) continue;
                if (!haveKey) {
                    if (p->isIdrNalu) { haveKey = true; keyTs = p->timestamp; keyBegin = i - 1; }
                }
                else if (!p->isIdrNalu || p->timestamp != keyTs) {
                    break;  // 已越过关键帧帧头
                }
                else {
                    keyBegin = i - 1;
                }
            }

            size_t begin = bufSize;
            if (haveKey) {
                begin = (winBegin < keyBegin) ? winBegin : keyBegin;
            }
            else if (winBegin < bufSize) {
                // 缓冲内无关键帧（GOP 超过缓冲窗口）：退回纯时间窗回溯，
                // 首个关键帧到达前仍无输出，记录警告便于定位
                begin = winBegin;
                LOG("[录像] tag=%s: 预录回溯范围内无关键帧，文件将在下一个关键帧处才有数据",
                    config_.tag.c_str());
            }

            for (size_t i = begin; i < bufSize; i++) {
                if (rtp_buffer_[i]) pre_packets.push_back(rtp_buffer_[i]);
            }
        }
        for (auto& p : pre_packets) {
            if (!p) continue;  // 防御：rtp_buffer_ 异常情况下跳过空指针
            // 预录包同样计入媒体时长范围（文件里确实包含预录内容）
            if (!rec_ctrl_.has_first_ts_) {
                rec_ctrl_.first_rtp_ts_ = p->timestamp;
                rec_ctrl_.has_first_ts_ = true;
            }
            rec_ctrl_.last_rtp_ts_ = p->timestamp;
            std::lock_guard<std::mutex> lock(record_queue_mutex_);
            record_queue_.push(p);
        }
        rec_ctrl_.preRecordingDone = true;
    }
    // 记录首末帧 RTP 时间戳，用于精确计算媒体时长
    if (!rec_ctrl_.has_first_ts_) {
        rec_ctrl_.first_rtp_ts_ = packet->timestamp;
        rec_ctrl_.has_first_ts_ = true;
    }
    rec_ctrl_.last_rtp_ts_ = packet->timestamp;
    {
        std::lock_guard<std::mutex> queueLock(record_queue_mutex_);
        record_queue_.push(packet);
    }
    record_queue_cv_.notify_one();
}

void StreamNode::flushRecordBuffer() {
    record_io_running_ = false;
    record_queue_cv_.notify_one();
    if (record_io_thread_.joinable()) {
        record_io_thread_.join();
    }
}

// 将单个 RTP 包中的 NAL 单元写入文件（由 I/O 线程调用，不含文件打开/关闭）
void StreamNode::writeRTPPacketToFile(std::shared_ptr<RTPPacket> pPkt, std::ofstream& ofs) {
    const std::vector<uint8_t>& payload = pPkt->payload;
    if (payload.empty()) return;

    // 录像编码未知（startRecord 早于 SDP 解析）时，用已缓存的参数集探测实际编码：
    // VPS 为 H.265 独有；H.265 SPS 首字节按 2 字节 NAL 头解释 type=33，H.264 SPS 为 0x67(type=7)。
    // onRecvOriginRtpPkt 在 SDP 解析后会把会话参数集同步到 last_sps_/last_vps_，
    // 故首个 RTP 包到达时探测必然可确定；此前包按 H.264 处理（firstWrite 丢弃到首个关键帧，无副作用）。
    if (rec_ctrl_.codec.empty()) {
        std::string detected;
        if (!last_vps_.empty()) {
            detected = "H265";
        } else if (!last_sps_.empty()) {
            detected = ((((uint8_t)last_sps_[0] >> 1) & 0x3F) == NAL_TYPE_H265_SPS) ? "H265" : "H264";
        }
        if (!detected.empty()) {
            rec_ctrl_.codec = detected;
            LOG("[录像] tag=%s: 探测到录像编码 %s", config_.tag.c_str(), detected.c_str());
        }
    }

    // H.264: 1 字节 NAL 头, type = payload[0] & 0x1F
    // H.265: 2 字节 NAL 头, type = (payload[0] >> 1) & 0x3F
    const bool isH265 = (rec_ctrl_.codec == "H265" || rec_ctrl_.codec == "HEVC");
    uint8_t nal_unit_type = isH265 ? ((payload[0] >> 1) & 0x3F) : (payload[0] & 0x1F);

    if (isH265) {
        // H.265 聚合包 AP：NAL 头(2) + [长度(2) + NAL]*n
        if (nal_unit_type == NAL_TYPE_H265_AP && payload.size() >= 4) {
            size_t off = 2;
            while (off + 2 <= payload.size()) {
                uint16_t L = (payload[off] << 8) | payload[off + 1];
                off += 2;
                if (L == 0) continue;
                if (off + L > payload.size()) break;
                const uint8_t* subNal = &payload[off];
                uint8_t sub_nal_type = (subNal[0] >> 1) & 0x3F;
                writeNALtoFile(sub_nal_type, (char*)subNal, L, ofs);
                off += L;
            }
        }
        // H.265 分片包 FU：NAL 头(2) + FU 头(1, 仅低 6 位为类型，其余为 start/end)
        else if (nal_unit_type == NAL_TYPE_H265_FU && payload.size() >= 3) {
            uint8_t fu_header = payload[2];
            bool start = (fu_header & 0x80) != 0;
            bool end   = (fu_header & 0x40) != 0;
            uint8_t fu_org_type = fu_header & 0x3F;
            // 重组 2 字节 NAL 头：保留原头的前 2 bit（forbidden+layer_id 高位）与第 2 字节
            uint8_t nal_header[2];
            nal_header[0] = (payload[0] & 0x81) | (fu_org_type << 1);
            nal_header[1] = payload[1];

            // 丢片保护：start 分片丢失时残片没有 NAL 头，继续拼接会写出损坏的 NAL
            if (!start && rec_ctrl_.fu_a_buffer_.empty()) return;

            if (start) {
                rec_ctrl_.fu_a_buffer_.clear();
                rec_ctrl_.fu_a_buffer_.push_back(nal_header[0]);
                rec_ctrl_.fu_a_buffer_.push_back(nal_header[1]);
            }
            rec_ctrl_.fu_a_buffer_.insert(rec_ctrl_.fu_a_buffer_.end(),
                payload.begin() + 3, payload.end());

            if (end) {
                writeNALtoFile(fu_org_type, rec_ctrl_.fu_a_buffer_.data(),
                    rec_ctrl_.fu_a_buffer_.size(), ofs);
            }
        }
        // H.265 单 NAL 包（payload 即完整 NAL，含 2 字节头）
        else {
            writeNALtoFile(nal_unit_type, (char*)payload.data(), payload.size(), ofs);
        }
        return;
    }

    // ---- H.264 ----
    if (nal_unit_type == NAL_TYPE_STAP_A && payload.size() >= 2) {
        size_t off = 1;
        while (off + 2 <= payload.size()) {
            uint16_t L = (payload[off] << 8) | payload[off + 1];
            off += 2;
            if (L == 0) continue;
            if (off + L > payload.size()) break;
            const uint8_t* subNal = &payload[off];
            uint8_t sub_nal_type = subNal[0] & 0x1F;
            writeNALtoFile(sub_nal_type, (char*)subNal, L, ofs);
            off += L;
        }
    }
    else if (nal_unit_type == NAL_TYPE_FU_A && payload.size() >= 2) {
        uint8_t fu_header = payload[1];
        bool start = (fu_header & 0x80) != 0;
        bool end   = (fu_header & 0x40) != 0;
        uint8_t fu_a_org_type = fu_header & 0x1F;
        uint8_t nal_header = (payload[0] & 0xE0) | fu_a_org_type;

        // 丢片保护：start 分片丢失时残片没有 NAL 头，继续拼接会写出损坏的
        // NAL（首字节错位，MP4 解析帧边界错乱），直接丢弃本片
        if (!start && rec_ctrl_.fu_a_buffer_.empty()) return;

        if (start) {
            rec_ctrl_.fu_a_buffer_.clear();
            rec_ctrl_.fu_a_buffer_.push_back(nal_header);
        }
        rec_ctrl_.fu_a_buffer_.insert(rec_ctrl_.fu_a_buffer_.end(),
            payload.begin() + 2, payload.end());

        if (end) {
            writeNALtoFile(fu_a_org_type, rec_ctrl_.fu_a_buffer_.data(),
                rec_ctrl_.fu_a_buffer_.size(), ofs);
        }
    }
    else {
        writeNALtoFile(nal_unit_type, (char*)payload.data(), payload.size(), ofs);
    }
}

// 录像独立 I/O 线程：从队列取包，批量写盘，常驻文件句柄
void StreamNode::threadRec_h264File() {
    //open record file
    std::ofstream ofs;
    LOG("[StreamServer]record io thread start, path=%s, empty=%d",
        rec_ctrl_.path.c_str(), rec_ctrl_.path.empty());
    if (!rec_ctrl_.path.empty()) {
#ifdef _WIN32
        ofs.open(pathToWide(rec_ctrl_.path), std::ios::binary | std::ios::app);
#else
        ofs.open(rec_ctrl_.path, std::ios::binary | std::ios::app);
#endif
        if (!ofs) {
            LOG("[error][StreamServer]start record,open record file fail, " + rec_ctrl_.path + ", " + std::string(strerror(errno)));
            return;
        }
        else {
            LOG("[StreamServer]start record,open record file success," + rec_ctrl_.path);
        }
    }
    else {
        LOG("[error][StreamServer]record io thread: path is empty, skip open");
    }

    std::vector<std::shared_ptr<RTPPacket>> batch;
    while (record_io_running_) {
        {
            std::unique_lock<std::mutex> lock(record_queue_mutex_);
            record_queue_cv_.wait_for(lock, std::chrono::milliseconds(500), [this] {
                return !record_queue_.empty() || !record_io_running_;
            });

            if (record_queue_.empty()) continue;

            while (!record_queue_.empty()) {
                batch.push_back(std::move(record_queue_.front()));
                record_queue_.pop();
            }
        }

        for (auto& p : batch) {
            if (!p) continue;  // 防御：极端情况下队列中混入空指针，跳过避免崩溃
            writeRTPPacketToFile(p, ofs);
        }
        ofs.flush();
        batch.clear();
    }

    // 诊断：循环结束后、close 之前检查
    LOG("[录像] io loop exited, ofs good=%d, tellp=%lld",
        (bool)ofs, (long long)ofs.tellp());
    ofs.close();
    // fsync：确保内核缓冲区的数据落盘，避免后续异步 remux 读到 0 字节
    // （Windows 下必须用宽字符路径：tag 含中文时 CreateFileA 打不开文件）
    {
#ifdef _WIN32
        HANDLE h = CreateFileW(pathToWide(rec_ctrl_.path).c_str(), GENERIC_READ, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, nullptr);
        if (h != INVALID_HANDLE_VALUE) { FlushFileBuffers(h); CloseHandle(h); }
#else
        int fd = open(rec_ctrl_.path.c_str(), O_RDONLY);
        if (fd >= 0) { fsync(fd); close(fd); }
#endif
    }
    // 诊断：检查文件实际大小（同样必须宽字符路径，否则中文路径误报 0）
    {
#ifdef _WIN32
        std::ifstream check(pathToWide(rec_ctrl_.path), std::ios::binary | std::ios::ate);
#else
        std::ifstream check(rec_ctrl_.path, std::ios::binary | std::ios::ate);
#endif
        size_t sz = check ? static_cast<size_t>(check.tellg()) : 0;
        LOG("[StreamServer]stop record,close record file," + rec_ctrl_.path
            + ",nal count=" + std::to_string(rec_ctrl_.nalCount)
            + ",file size=" + std::to_string(sz));
    }
}

// 解析 slice_header 首个字段 first_mb_in_slice（Exp-Golomb 无符号），
// ==0 表示一帧（access unit）的第一个 slice；多 slice 帧的后续 slice 不重复计数。
// 与 mp4Writer.cpp isFirstSliceOfPicture 判定规则保持一致（含 emulation prevention 处理）。
static bool isNewFrameSlice(const char* nal, size_t size) {
    if (size <= 1) return true;

    // 去 emulation prevention bytes，跳过 NAL header 后读第一个 Exp-Golomb 值
    std::vector<uint8_t> rbsp;
    rbsp.reserve(size - 1);
    int zeroCount = 0;
    for (size_t i = 1; i < size; ++i) {
        uint8_t byte = static_cast<uint8_t>(nal[i]);
        if (zeroCount >= 2 && byte == 0x03) {
            zeroCount = 0;
            continue;
        }
        rbsp.push_back(byte);
        if (byte == 0x00) ++zeroCount;
        else zeroCount = 0;
    }
    if (rbsp.empty()) return true;

    size_t bitPos = 0;
    auto getBit = [&]() -> int {
        if (bitPos >= rbsp.size() * 8) return 0;
        int bit = (rbsp[bitPos >> 3] >> (7 - (bitPos & 7))) & 1;
        bitPos++;
        return bit;
    };
    int leadingZeros = 0;
    while (bitPos < rbsp.size() * 8 && getBit() == 0) leadingZeros++;
    if (bitPos >= rbsp.size() * 8) return true;  // 数据耗尽，与 mp4Writer readUE 耗尽返回 0 的判定一致
    if (leadingZeros == 0) return true;  // first_mb_in_slice == 0
    unsigned int val = 0;
    for (int i = 0; i < leadingZeros; i++)
        val = (val << 1) | getBit();
    return ((1u << leadingZeros) - 1 + val) == 0;
}

// H.265 slice header 第一个字段 first_slice_segment_in_pic_flag（1 bit），
// ==1 表示一帧的第一个 slice。跳过 2 字节 NAL 头后读首 bit。
// 与 mp4Writer.cpp isFirstSliceOfPictureHevc 判定规则保持一致。
static bool isNewFrameSliceH265(const char* nal, size_t size) {
    if (size <= 2) return true;

    std::vector<uint8_t> rbsp;
    rbsp.reserve(size - 2);
    int zeroCount = 0;
    for (size_t i = 2; i < size; ++i) {
        uint8_t byte = static_cast<uint8_t>(nal[i]);
        if (zeroCount >= 2 && byte == 0x03) {
            zeroCount = 0;
            continue;
        }
        rbsp.push_back(byte);
        if (byte == 0x00) ++zeroCount;
        else zeroCount = 0;
    }
    if (rbsp.empty()) return true;

    // first_slice_segment_in_pic_flag = rbsp 首个字节的最高位
    return (rbsp[0] & 0x80) != 0;
}

void StreamNode::writeNALtoFile(uint8_t nal_type, char* nal, size_t size, std::ofstream& ofs) {
    // 录像编码（H264/H265），startRecord 时从会话 codec 确定
    const bool isH265 = (rec_ctrl_.codec == "H265" || rec_ctrl_.codec == "HEVC");

    // 记录 SPS VUI 帧率供 MP4 转换使用（丢包时帧数/时长推算会偏差）。
    // 每次收到 SPS 都更新，与 mp4Writer 取文件内最后一个 SPS 的行为一致；解析失败保持原值。
    // 置于 firstWrite 检查之前：首个 SPS 可能先于首个 IDR 到达并被跳过，不能漏解析。
    const uint8_t spsType = isH265 ? NAL_TYPE_H265_SPS : NAL_TYPE_SPS;
    if (nal_type == spsType) {
        double fps = isH265 ? mp4::parseHevcSpsFps((const uint8_t*)nal, size)
                            : mp4::parseSpsFps((const uint8_t*)nal, size);
        if (fps > 0.0) {
            rec_ctrl_.sps_fps = fps;
            LOG("[录像] tag=%s: SPS 帧率 %.2f fps", config_.tag.c_str(), fps);
        }
    }

    // H.265 IRAP（16-23）对应 H.264 IDR，作为可随机访问点
    const bool isKeyNal = isH265 ? (nal_type >= 16 && nal_type <= 23)
                                 : (nal_type == NAL_TYPE_IDR);

    //文件头写入关键帧
    if (rec_ctrl_.firstWrite) {
        if (!isKeyNal) {
            return;
        }
    }
    rec_ctrl_.firstWrite = false;

    // VCL 帧计数（新帧首个 slice 计为一帧，多 slice 不重复计数，与 MP4 分帧一致）
    // H.265 所有 0-31 的 NAL 均为 VCL；H.264 仅 IDR/NON_IDR
    // 放在 firstWrite 检查后：只数实际写入文件的帧，与 MP4 解析的文件内容对应
    const bool isVcl = isH265 ? (nal_type <= 31)
                              : (nal_type == NAL_TYPE_IDR || nal_type == NAL_TYPE_NON_IDR);
    if (isVcl) {
        bool isNewSlice = isH265 ? isNewFrameSliceH265(nal, size) : isNewFrameSlice(nal, size);
        if (isNewSlice) {
            rec_ctrl_.frame_count++;
        }
    }
    rec_ctrl_.isLastIdrNal = rec_ctrl_.isIdrNal;
    rec_ctrl_.isIdrNal = isKeyNal;

    const uint8_t start_code[4] = { 0x00, 0x00, 0x00, 0x01 };

    // 切换到关键帧前写入参数集（由 onRecvOriginRtpPkt 实时更新缓存）
    if (rec_ctrl_.isLastIdrNal == false && rec_ctrl_.isIdrNal == true) {
        // H.265 先写 VPS，再 SPS/PPS
        if (isH265 && !last_vps_.empty()) {
            ofs.write((const char*)start_code, sizeof(start_code));
            ofs.write(last_vps_.data(), last_vps_.size());
        }
        if (!last_sps_.empty()) {
            // 兜底：RTP 流未直接携带 SPS 时（SPS 仅存在于 SDP/缓存），从写入的 SPS 解析帧率
            if (rec_ctrl_.sps_fps <= 0.0) {
                double fps = isH265 ? mp4::parseHevcSpsFps((const uint8_t*)last_sps_.data(), last_sps_.size())
                                    : mp4::parseSpsFps((const uint8_t*)last_sps_.data(), last_sps_.size());
                if (fps > 0.0) {
                    rec_ctrl_.sps_fps = fps;
                    LOG("[录像] tag=%s: SPS 帧率 %.2f fps (cached)", config_.tag.c_str(), fps);
                }
            }
            ofs.write((const char*)start_code, sizeof(start_code));
            ofs.write(last_sps_.data(), last_sps_.size());
        }
        if (!last_pps_.empty()) {
            ofs.write((const char*)start_code, sizeof(start_code));
            ofs.write(last_pps_.data(), last_pps_.size());
        }
    }

    ofs.write((const char*)start_code, sizeof(start_code));
    ofs.write((const char*)nal, size);
    rec_ctrl_.nalCount++;
    if (!ofs) {
        LOG("[error][录像] tag=%s: write failed at nal #%zu, path=%s",
            config_.tag.c_str(), rec_ctrl_.nalCount, rec_ctrl_.path.c_str());
    }
    // 诊断：首个 NAL 写入后检查文件写入位置
    if (rec_ctrl_.nalCount == 1) {
        auto pos = ofs.tellp();
        LOG("[录像] tag=%s: first NAL written, tellp=%lld, nal size=%zu",
            config_.tag.c_str(), (long long)pos, size);
    }
}
