`include "pcie_pkg.sv"   // 临时兜底，确保 pcie_pkg 先被定义
interface pcie_if #(parameter ADDR_W=32, DATA_W=32, LEN_W=10) (input logic clk, rst_n);//#( … )：参数列表，用来参数化接口里信号的位宽等。( … )：端口列表，把外部的 clk、rst_n 传进 interface，供里面的 SVA、covergroup 和任务使用

  import pcie_pkg::*;
  // Request: MRd/MWr/Cfg*
  logic        req_valid, req_ready;//宽度为1，表示握手信号
  tlp_type_e  req_type;    // 事务类型，0:MRd 1:MWr 2:CfgRd 3:CfgWr（示例）
  logic [ADDR_W-1:0] req_addr;// 低位地址，32位或64位。目标地址；在 valid && !ready 期间必须保持稳定
  logic [LEN_W-1:0]  req_len;     // 传输长度，以DW或字节计，统一即可。
  logic [7:0]        req_tag;     // MRd/Cfg* 用
  logic [DATA_W-1:0] req_data;    // 仅 MWr 有效

  // Completion: Cpl/CplD（读必有；写可选“验证友好”状态）
  logic        cpl_valid, cpl_ready;//
  logic [2:0]  cpl_status;  // 完成状态，0=OK
  logic [7:0]  cpl_tag;// MRd/Cfg* 用
  logic [DATA_W-1:0] cpl_data;    // 仅 CplD 有

  // ---------- 默认驱动 ----------
  task automatic drive_defaults(bit accept_cpl = 1'b1);
    req_valid <= 1'b0;
    req_type  <= TLP_MRd;      // 默认给个合法值，避免 X 传播  [ADDED]
    req_addr  <= '0;
    req_len   <= '0;
    req_tag   <= '0;
    req_data  <= '0;
    cpl_ready <= accept_cpl;   // [ADDED]
    cpl_valid <= 1'b0;         // [ADDED]
    cpl_status<= '0;           // [ADDED]
    cpl_tag   <= '0;           // [ADDED]
    cpl_data  <= '0;           // [ADDED]
  endtask

  // ---------- SVA（握手稳定性） ----------
  `define DISABLE_IF disable iff(!rst_n)// 禁用断言和覆盖率，除非 rst_n 为 1
  // 在 valid=1 且 ready=0 的等待期，信号一旦变化就违规（同拍判定）
  property p_stable_during_wait(logic v, logic r, logic [$bits(req_data)-1:0] sig);
    @(posedge clk) `DISABLE_IF
      (v && !r) |-> $stable(sig) until_with r;
  endproperty

  // [CHANGED] valid 在等待期不能掉（之前写法矛盾导致永不触发）
  property p_no_drop_valid_while_wait(logic v, logic r);
    @(posedge clk) `DISABLE_IF
      (v && !r) |-> v until_with r;
  endproperty

    // === req 侧断言 ===
  a_req_valid_hold  : assert property (p_no_drop_valid_while_wait(req_valid, req_ready))
    else $fatal(1, "SVA a_req_valid_hold violated @%0t", $time);

  a_req_type_stable : assert property (p_stable_during_wait(req_valid, req_ready, req_type))
    else $fatal(1, "SVA a_req_type_stable violated @%0t", $time);

  a_req_addr_stable : assert property (p_stable_during_wait(req_valid, req_ready, req_addr))
    else $fatal(1, "SVA a_req_addr_stable violated @%0t", $time);

  a_req_len_stable  : assert property (p_stable_during_wait(req_valid, req_ready, req_len))
    else $fatal(1, "SVA a_req_len_stable violated @%0t", $time);

  a_req_tag_stable  : assert property (p_stable_during_wait(req_valid, req_ready, req_tag))
    else $fatal(1, "SVA a_req_tag_stable violated @%0t", $time);

  a_req_data_stable : assert property (p_stable_during_wait(req_valid, req_ready, req_data))
    else $fatal(1, "SVA a_req_data_stable violated @%0t", $time);

  // === cpl 侧断言（如果也需要稳定性校验） ===
  a_cpl_valid_hold    : assert property (p_no_drop_valid_while_wait(cpl_valid, cpl_ready))
    else $fatal(1, "SVA a_cpl_valid_hold violated @%0t", $time);

  a_cpl_status_stable : assert property (p_stable_during_wait(cpl_valid, cpl_ready, cpl_status))
    else $fatal(1, "SVA a_cpl_status_stable violated @%0t", $time);

  a_cpl_tag_stable    : assert property (p_stable_during_wait(cpl_valid, cpl_ready, cpl_tag))
    else $fatal(1, "SVA a_cpl_tag_stable violated @%0t", $time);

  a_cpl_data_stable   : assert property (p_stable_during_wait(cpl_valid, cpl_ready, cpl_data))
    else $fatal(1, "SVA a_cpl_data_stable violated @%0t", $time);
  // ---------- 覆盖 ----------
  covergroup cg_tlp @(posedge clk);
    coverpoint req_type {
      bins rd={TLP_MRd}; bins wr={TLP_MWr}; bins cfg_rd={TLP_CfgRd}; bins cfg_wr={TLP_CfgWr};
    }
    coverpoint req_len  { bins len_small={[1:4]}; bins len_mid={[5:16]}; bins len_large={[17:64]}; }
    cross req_type, req_len;
  endgroup
  cg_tlp cov = new();

endinterface
