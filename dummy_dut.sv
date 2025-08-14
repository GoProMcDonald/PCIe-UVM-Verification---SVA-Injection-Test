  module dummy_dut #(parameter ADDR_W=32, DATA_W=32, LEN_W=10) (pcie_if ifc);//这里的 ifc 就是接口实例的句柄
    import pcie_pkg::*;
    // 简易内存：地址低12位做索引
    // 参数化内存地址位宽，统一索引位
    localparam int MEM_AW = 12;         // 2^12 = 4096
    logic [DATA_W-1:0] mem [0:(1<<MEM_AW)-1];

    // 初始化内存，避免读出 X
    integer i;

      // ---------------- 握手时序控制（关键） ----------------
    typedef enum logic [1:0] {IDLE, WAIT, ACCEPT} st_e;  // [ADDED]
    st_e st;                                             // [ADDED]
    int  wait_cnt;                                       // [ADDED]


    // pipeline for MRd
    logic        r_mrd_vld_d1, r_mrd_vld_d2;// MRd 有效标志
    logic [7:0]  r_mrd_tag_d1, r_mrd_tag_d2;// MRd 的 tag
    logic [ADDR_W-1:0] r_mrd_addr_d1, r_mrd_addr_d2;// MRd 的地址
    logic [DATA_W-1:0] r_mrd_data_d1, r_mrd_data_d2;


    always_ff @(posedge ifc.clk or negedge ifc.rst_n) begin
      if(!ifc.rst_n) begin// 如果复位信号为低

            // ====== 内存初始化（避免读出 X）======
      for (i = 0; i < (1<<MEM_AW); i++) begin
        mem[i] <= '0;              // 或者 <= i; 任选一个确定值
      end

        // 复位所有信号
        ifc.cpl_valid   <= 1'b0;
        ifc.cpl_status  <= 3'd0;
        ifc.cpl_tag     <= '0;
        ifc.cpl_data    <= '0;

        r_mrd_vld_d1    <= 1'b0;
        r_mrd_vld_d2    <= 1'b0;
        r_mrd_tag_d1    <= '0;// 复位 MRd 的 tag
        r_mrd_tag_d2    <= '0;// 复位 MRd 的 tag
        r_mrd_addr_d1   <= '0;
        r_mrd_addr_d2   <= '0;
        r_mrd_data_d1   <= '0;        // ★ 新增复位
        r_mrd_data_d2   <= '0;
        st       <= IDLE;        // [ADDED]
        wait_cnt <= 0;           // [ADDED]
        ifc.req_ready <= 1'b0;   // [ADDED] 复位时保持 not ready
      end 
      else begin// 如果复位信号为高
        // 捕获 MRd
                // ---------------- 握手状态机（形成等待期） ----------------
      unique case (st)
        IDLE: begin
          ifc.req_ready <= 1'b0;            // 默认不 ready
          if (ifc.req_valid) begin          // 看到对端拉高 valid
            st       <= WAIT;
            wait_cnt <= 2;                  // [ADDED] 等两拍，保证存在 valid=1 && ready=0 的等待期
          end
        end

        WAIT: begin
          ifc.req_ready <= 1'b0;
          if (wait_cnt == 0) st <= ACCEPT;
          else wait_cnt <= wait_cnt - 1;
        end

        ACCEPT: begin
          ifc.req_ready <= 1'b1;            // [ADDED] 给一拍 ready=1 完成握手
          st <= IDLE;
        end
      endcase
        r_mrd_vld_d1  <= (ifc.req_valid && ifc.req_ready && ifc.req_type == TLP_MRd);// 如果请求有效且准备就绪，且类型为 MRd，则设置 r_mrd_vld_d1 为 1
        if (ifc.req_valid && ifc.req_ready && ifc.req_type == TLP_MRd) begin//
          r_mrd_tag_d1  <= ifc.req_tag;// 捕获 MRd 的 tag
          r_mrd_addr_d1 <= ifc.req_addr;// 捕获 MRd 的地址
          r_mrd_data_d1  <= mem[ifc.req_addr[MEM_AW+1:2]] ^ 32'hDEAD_BEEF;
          $display("[%0t] MRd cap: addr=0x%08h tag=0x%0h", $time, ifc.req_addr, ifc.req_tag);
        end
        //流水推进到第 2 级
        r_mrd_vld_d2  <= r_mrd_vld_d1;// 将 r_mrd_vld_d1 的值传递到 r_mrd_vld_d2
        r_mrd_tag_d2  <= r_mrd_tag_d1;// 将 r_mrd_tag_d1 的值传递到 r_mrd_tag_d2
        r_mrd_addr_d2 <= r_mrd_addr_d1;// 将 r_mrd_addr_d1 的值传递到 r_mrd_addr_d2
        r_mrd_data_d2  <= r_mrd_data_d1;     

        // MWr 直接写
        if (ifc.req_valid && ifc.req_ready && ifc.req_type == TLP_MWr)
          mem[ifc.req_addr[MEM_AW+1:2]] <= ifc.req_data;
        end

        // 两拍后产生 Completion with Data
        ifc.cpl_valid <= r_mrd_vld_d2;// 如果 r_mrd_vld_d2 为 1，则表示有 MRd 请求完成
        ifc.cpl_status<= 3'd0;// 完成状态为 0，表示 OK
        ifc.cpl_tag   <= r_mrd_tag_d2;// 设置完成的 tag 为 r_mrd_tag_d2
        ifc.cpl_data   <= r_mrd_vld_d2 ? r_mrd_data_d2 : '0; 
      end
  endmodule

