`include "src/boom/SmallBoom.v"
`include "src/boom/BOOM_mem.v"
`include "src/boom/plusarg_reader.v"

// 0 for sandboxing, 1 for constant-time
`define CONTRACT 1
`define SANDBOX 0
`define CT 1

module top(
    input clk,
    input rst
);
// 32个rob条目需要5位来表示
reg [4:0] ROB_tail_1, ROB_tail_2;
wire [4:0] new_tail_1 = (copy1.core.rob._com_idx_T & 
            ((copy1.core.rob.rob_tail !== copy1.core.rob.rob_head) | copy1.core.rob.maybe_full)) ? 
            copy1.core.rob._rob_tail_T_1 : 
            (~(copy1.core.rob._com_idx_T & copy1.core.rob._full_T & copy1.core.rob._finished_committing_row_T_6) ? 
            (copy1.core.rob.io_brupdate_b2_mispredict ? copy1.core.rob._rob_tail_T_4 : 
            copy1.core.rob._GEN_11100) : copy1.core.rob.rob_tail);
wire [4:0] new_tail_2 = (copy2.core.rob._com_idx_T & ((copy2.core.rob.rob_tail !== copy2.core.rob.rob_head) | copy2.core.rob.maybe_full)) ? copy2.core.rob._rob_tail_T_1 : (~(copy2.core.rob._com_idx_T & copy2.core.rob._full_T & copy2.core.rob._finished_committing_row_T_6) ? (copy2.core.rob.io_brupdate_b2_mispredict ? copy2.core.rob._rob_tail_T_4 : copy2.core.rob._GEN_11100) : copy2.core.rob.rob_tail);
reg stall_1, stall_2, finish_1, finish_2, commit_deviation, addr_deviation, invalid_program;
reg init;
// Shadow Logic for CT Contract
// 这里的设计表示有32个rob条目
reg [63:0] rs1_data_1 [31:0];
reg [63:0] rs1_data_2 [31:0];
reg [63:0] rs2_data_1 [31:0];
reg [63:0] rs2_data_2 [31:0];
reg [39:0] mem_addr_1 [31:0];
reg [39:0] mem_addr_2 [31:0];
reg [31:0] is_br_1, is_br_2, is_jalr_1, is_jalr_2, is_muldiv_1, is_muldiv_2, is_mem_1, is_mem_2;

// ISA observations
// For branch and muldiv, compare both rs1 and rs2; for jalr, only compare rs1
// 对于sandbox合约：不能把秘密数据加载到寄存器中。这里使用rob debug head中的写入寄存器中的值作为判定标准。
/** 
对于constant-time合约：不能有依赖秘密数据的分支和依赖秘密数据的地址访问。
具体到代码中的实现是：
1. 如果rob head的指令是branch指令或者muldiv指令，那么他们源寄存器1和2的内容都不能相等；
2. 如果rob head指令是jalr指令，那么他们源寄存器1中的内容不能相同；
3. 如果是内存相关的指令，那么他们的内存操作的目标地址不能相同。
**/
// 这里比较的都是rob head中将要提交的地址。和判断是否产生uarch差异所使用的内存地址是不同时期的，
// （它那个阶段使用的是当前时刻的所要访问的内存地址，也就是即时的，一旦发现差异就立刻表示发生微架构差异）
wire isa_deviation = (`CONTRACT == `SANDBOX) ? (copy1.core.rob.rob_head_wdata != copy2.core.rob.rob_head_wdata)
                    : (`CONTRACT == `CT) ? ((is_br_1[copy1.core.rob.rob_head] || is_muldiv_1[copy1.core.rob.rob_head]) && (rs1_data_1[copy1.core.rob.rob_head]!=rs1_data_2[copy2.core.rob.rob_head] || rs2_data_1[copy1.core.rob.rob_head]!=rs2_data_2[copy2.core.rob.rob_head]))
                                        || (is_jalr_1[copy1.core.rob.rob_head] && (rs1_data_1[copy1.core.rob.rob_head]!=rs1_data_2[copy2.core.rob.rob_head]))
                                        || (is_mem_1[copy1.core.rob.rob_head] && (mem_addr_1[copy1.core.rob.rob_head]!=mem_addr_2[copy2.core.rob.rob_head]))
                    : 0;
always @(posedge clk) begin
    if (rst) begin
        is_br_1 <= 0;
        is_br_2 <= 0;
        is_jalr_1 <= 0;
        is_jalr_2 <= 0;
        is_muldiv_1 <= 0;
        is_muldiv_2 <= 0;
        is_mem_1 <= 0;
        is_mem_2 <= 0;
    end
    else begin
        // 通过观察rob tail条目中的uop来提取指令的类型
        if (copy1.core.rob.io_enq_valids_0) begin
            is_br_1[copy1.core.rob.rob_tail] <= copy1.core.rob.io_enq_uops_0_is_br;
            is_jalr_1[copy1.core.rob.rob_tail] <= copy1.core.rob.io_enq_uops_0_is_jalr;
            is_muldiv_1[copy1.core.rob.rob_tail] <= 0;
            is_mem_1[copy1.core.rob.rob_tail] <= 0;
        end
        if (copy2.core.rob.io_enq_valids_0) begin
            is_br_2[copy2.core.rob.rob_tail] <= copy2.core.rob.io_enq_uops_0_is_br;
            is_jalr_2[copy2.core.rob.rob_tail] <= copy2.core.rob.io_enq_uops_0_is_jalr;
            is_muldiv_2[copy2.core.rob.rob_tail] <= 0;
            is_mem_2[copy2.core.rob.rob_tail] <= 0;
        end
        // 提取寄存器中的值和mem操作的目标内存地址；并且以rob的id数作为该寄存器位的索引
        if (copy1.core.csr_exe_unit.alu.io_req_valid && (copy1.core.csr_exe_unit.alu.io_req_bits_uop_is_br || copy1.core.csr_exe_unit.alu.io_req_bits_uop_is_jalr)) begin
            rs1_data_1[copy1.core.csr_exe_unit.alu.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.alu.io_req_bits_rs1_data;
            rs2_data_1[copy1.core.csr_exe_unit.alu.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.alu.io_req_bits_rs2_data;
        end
        if (copy2.core.csr_exe_unit.alu.io_req_valid && (copy2.core.csr_exe_unit.alu.io_req_bits_uop_is_br || copy2.core.csr_exe_unit.alu.io_req_bits_uop_is_jalr)) begin
            rs1_data_2[copy2.core.csr_exe_unit.alu.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.alu.io_req_bits_rs1_data;
            rs2_data_2[copy2.core.csr_exe_unit.alu.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.alu.io_req_bits_rs2_data;
        end
        if (copy1.core.csr_exe_unit.imul.io_req_valid) begin
            is_muldiv_1[copy1.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= 1;
            rs1_data_1[copy1.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.imul.io_req_bits_rs1_data;
            rs2_data_1[copy1.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.imul.io_req_bits_rs2_data;
        end
        if (copy2.core.csr_exe_unit.imul.io_req_valid) begin
            is_muldiv_2[copy2.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= 1;
            rs1_data_2[copy2.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.imul.io_req_bits_rs1_data;
            rs2_data_2[copy2.core.csr_exe_unit.imul.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.imul.io_req_bits_rs2_data;
        end
        if (copy1.core.csr_exe_unit.div.io_req_valid) begin
            is_muldiv_1[copy1.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= 1;
            rs1_data_1[copy1.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.div.io_req_bits_rs1_data;
            rs2_data_1[copy1.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= copy1.core.csr_exe_unit.div.io_req_bits_rs2_data;
        end
        if (copy2.core.csr_exe_unit.div.io_req_valid) begin
            is_muldiv_2[copy2.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= 1;
            rs1_data_2[copy2.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.div.io_req_bits_rs1_data;
            rs2_data_2[copy2.core.csr_exe_unit.div.io_req_bits_uop_rob_idx] <= copy2.core.csr_exe_unit.div.io_req_bits_rs2_data;
        end
        if (copy1.lsu.io_core_exe_0_req_valid && (copy1.lsu.io_core_exe_0_req_bits_uop_ctrl_is_sta||copy1.lsu.io_core_exe_0_req_bits_uop_ctrl_is_load)) begin
            is_mem_1[copy1.lsu.io_core_exe_0_req_bits_uop_rob_idx] <= 1;
            mem_addr_1[copy1.lsu.io_core_exe_0_req_bits_uop_rob_idx] <= copy1.lsu.io_core_exe_0_req_bits_addr;
        end
        if (copy2.lsu.io_core_exe_0_req_valid && (copy2.lsu.io_core_exe_0_req_bits_uop_ctrl_is_sta||copy2.lsu.io_core_exe_0_req_bits_uop_ctrl_is_load)) begin
            is_mem_2[copy2.lsu.io_core_exe_0_req_bits_uop_rob_idx] <= 1;
            mem_addr_2[copy2.lsu.io_core_exe_0_req_bits_uop_rob_idx] <= copy2.lsu.io_core_exe_0_req_bits_addr;
        end
    end
end

always @(posedge clk) begin
    if (rst) begin
        init <= 1;
    end else if (init) begin
        init <= 0;
    end
end


BoomTile copy1 ( 
    .clock(stall_1 ? 0 : clk),
    .reset(rst),
    .auto_int_local_in_3_0(0),
    .auto_int_local_in_2_0(0),
    .auto_int_local_in_1_0(0),
    .auto_int_local_in_1_1(0),
    .auto_int_local_in_0_0(0),
    .auto_hartid_in(0),
    .auto_tl_other_masters_out_a_ready(0),
    .auto_tl_other_masters_out_b_valid(0),
    .auto_tl_other_masters_out_b_bits_opcode(0),
    .auto_tl_other_masters_out_b_bits_param(0),
    .auto_tl_other_masters_out_b_bits_size(0),
    .auto_tl_other_masters_out_b_bits_source(0),
    .auto_tl_other_masters_out_b_bits_address(0),
    .auto_tl_other_masters_out_b_bits_mask(0),
    .auto_tl_other_masters_out_b_bits_corrupt(0),
    .auto_tl_other_masters_out_c_ready(0),
    .auto_tl_other_masters_out_d_valid(0),
    .auto_tl_other_masters_out_d_bits_opcode(0),
    .auto_tl_other_masters_out_d_bits_param(0),
    .auto_tl_other_masters_out_d_bits_size(0),
    .auto_tl_other_masters_out_d_bits_source(0),
    .auto_tl_other_masters_out_d_bits_sink(0),
    .auto_tl_other_masters_out_d_bits_denied(0),
    .auto_tl_other_masters_out_d_bits_data(0),
    .auto_tl_other_masters_out_d_bits_corrupt(0),
    .auto_tl_other_masters_out_e_ready(0)
  );

BoomTile copy2 ( 
    .clock(stall_2 ? 0 : clk),
    .reset(rst),
    .auto_int_local_in_3_0(0),
    .auto_int_local_in_2_0(0),
    .auto_int_local_in_1_0(0),
    .auto_int_local_in_1_1(0),
    .auto_int_local_in_0_0(0),
    .auto_hartid_in(0),
    .auto_tl_other_masters_out_a_ready(0),
    .auto_tl_other_masters_out_b_valid(0),
    .auto_tl_other_masters_out_b_bits_opcode(0),
    .auto_tl_other_masters_out_b_bits_param(0),
    .auto_tl_other_masters_out_b_bits_size(0),
    .auto_tl_other_masters_out_b_bits_source(0),
    .auto_tl_other_masters_out_b_bits_address(0),
    .auto_tl_other_masters_out_b_bits_mask(0),
    .auto_tl_other_masters_out_b_bits_corrupt(0),
    .auto_tl_other_masters_out_c_ready(0),
    .auto_tl_other_masters_out_d_valid(0),
    .auto_tl_other_masters_out_d_bits_opcode(0),
    .auto_tl_other_masters_out_d_bits_param(0),
    .auto_tl_other_masters_out_d_bits_size(0),
    .auto_tl_other_masters_out_d_bits_source(0),
    .auto_tl_other_masters_out_d_bits_sink(0),
    .auto_tl_other_masters_out_d_bits_denied(0),
    .auto_tl_other_masters_out_d_bits_data(0),
    .auto_tl_other_masters_out_d_bits_corrupt(0),
    .auto_tl_other_masters_out_e_ready(0)
  );

wire commit1 = copy1.core.rob.io_commit_valids_0;
wire commit2 = copy2.core.rob.io_commit_valids_0;
// LSU模块向DCache发出的数据请求的地址
wire [39:0] addr1 = copy1.lsu.io_dmem_req_bits_0_bits_addr;
wire [39:0] addr2 = copy2.lsu.io_dmem_req_bits_0_bits_addr;
// Shadow Logic
always @(posedge clk) begin
    if (rst) begin
        stall_1 <= 0;
        stall_2 <= 0;
        finish_1 <= 0;
        finish_2 <= 0;
        commit_deviation <= 0;
        invalid_program <= 0;
    end
    else begin
        if (!stall_1 && !stall_2 && commit1 && commit2) begin
            if (isa_deviation)
                invalid_program <= 1;
        end
        // 如果两个模型都没有stall且commit1首先提交了，那么此时要阻塞cpu1，且说明他们在微架构上产生了差异
        else if (!stall_1 && !stall_2 && commit1 && !commit2) begin
            stall_1 <= 1;
            commit_deviation <= 1;
            // 如果没有微架构上的差异，那么需要将tail的内容提取出来
            // (但下面这个分支逻辑上永远也不会被执行)
            if (!(commit_deviation || addr_deviation)) begin
                ROB_tail_1 <= copy1.core.rob.rob_tail;
                ROB_tail_2 <= copy2.core.rob.rob_tail;
            end
        end
        // 和上一条相反的情况
        else if (!stall_1 && !stall_2 && !commit1 && commit2) begin
            stall_2 <= 1;
            commit_deviation <= 1;
            if (!(commit_deviation || addr_deviation)) begin
                ROB_tail_1 <= copy1.core.rob.rob_tail;
                ROB_tail_2 <= copy2.core.rob.rob_tail;
            end
        end
        // 如果cpu1被阻塞，且cpu2没有被阻塞但是commit2提交了。此时需要解除cpu1的阻塞
        else if (stall_1 && !stall_2 && commit2) begin
            if (isa_deviation)
                invalid_program <= 1;
            stall_1 <= 0;
        end
        // 和上一条相反的情况
        else if (!stall_1 && stall_2 && commit1) begin
            if (isa_deviation)
                invalid_program <= 1;
            stall_2 <= 0;
        end

        // Memory address deviation
        // 如果访问的内存地址不同，需要将addr_deviation置为1。并记录此时rob tail的位置
        if (!commit_deviation && addr1 != addr2 && !addr_deviation) begin
            addr_deviation <= 1;
            ROB_tail_1 <= copy1.core.rob.rob_tail;
            ROB_tail_2 <= copy2.core.rob.rob_tail;
        end

        // Upon tail rollback, update the recorded tail
        if (new_tail_1 < ROB_tail_1)
            ROB_tail_1 <= new_tail_1;
        if (new_tail_2 < ROB_tail_2)
            ROB_tail_2 <= new_tail_2;

        // Drain the ROB
        // 如果发生了提交差异或者地址差异，而且rob已经将ROB_tail中记录的指令完成提交，那么表示已完成执行
        if ((commit_deviation || addr_deviation) && (commit1 && copy1.core.rob.rob_head==ROB_tail_1-1 || copy1.core.rob.rob_head >= ROB_tail_1))
            finish_1 <= 1;
        if ((commit_deviation || addr_deviation) && (commit2 && copy2.core.rob.rob_head==ROB_tail_2-1 || copy2.core.rob.rob_head >= ROB_tail_2))
            finish_2 <= 1;
    end
end

endmodule