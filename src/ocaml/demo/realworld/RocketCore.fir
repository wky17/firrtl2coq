circuit RocketCore : 
  module RocketCore : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip interrupts : {debug : UInt<1>, mtip : UInt<1>, msip : UInt<1>, meip : UInt<1>, seip : UInt<1>},  flip hartid : UInt<64>, imem : {req : {valid : UInt<1>, bits_wky : {pc : UInt<40>, speculative : UInt<1>}},  flip resp : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {btb : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}, pc : UInt<40>, data : UInt<32>, mask : UInt<2>, xcpt_if : UInt<1>, replay : UInt<1>}}, btb_update : {valid : UInt<1>, bits_wky : {prediction : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}, pc : UInt<39>, target : UInt<39>, taken : UInt<1>, isValid : UInt<1>, isJump : UInt<1>, isReturn : UInt<1>, br_pc : UInt<39>}}, bht_update : {valid : UInt<1>, bits_wky : {prediction : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}, pc : UInt<39>, taken : UInt<1>, mispredict : UInt<1>}}, ras_update : {valid : UInt<1>, bits_wky : {isCall : UInt<1>, isReturn : UInt<1>, returnAddr : UInt<39>, prediction : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}}}, flush_icache : UInt<1>, flush_tlb : UInt<1>,  flip npc : UInt<40>,  flip acquire : UInt<1>}, dmem : {req : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {addr : UInt<40>, tag : UInt<7>, cmd : UInt<5>, typ : UInt<3>, phys : UInt<1>, data : UInt<64>}}, s1_kill : UInt<1>, s1_data : UInt<64>,  flip s2_nack : UInt<1>,  flip acquire : UInt<1>,  flip release : UInt<1>,  flip resp : {valid : UInt<1>, bits_wky : {addr : UInt<40>, tag : UInt<7>, cmd : UInt<5>, typ : UInt<3>, data : UInt<64>, replay : UInt<1>, has_data : UInt<1>, data_word_bypass : UInt<64>, store_data : UInt<64>}},  flip replay_next : UInt<1>,  flip xcpt : {ma : {ld : UInt<1>, st : UInt<1>}, pf : {ld : UInt<1>, st : UInt<1>}}, invalidate_lr : UInt<1>,  flip ordered : UInt<1>},  flip ptw : { flip ptbr : {mode : UInt<4>, asid : UInt<16>, ppn : UInt<44>},  flip invalidate_wky : UInt<1>,  flip status : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}},  flip fpu : { flip inst_wky : UInt<32>,  flip fromint_data : UInt<64>,  flip fcsr_rm : UInt<3>, fcsr_flags : {valid : UInt<1>, bits_wky : UInt<5>}, store_data : UInt<64>, toint_data : UInt<64>,  flip dmem_resp_val : UInt<1>,  flip dmem_resp_type : UInt<3>,  flip dmem_resp_tag : UInt<5>,  flip dmem_resp_data : UInt<64>,  flip valid : UInt<1>, fcsr_rdy : UInt<1>, nack_mem : UInt<1>, illegal_rm : UInt<1>,  flip killx : UInt<1>,  flip killm : UInt<1>, dec : {cmd : UInt<5>, ldst : UInt<1>, wen : UInt<1>, ren1 : UInt<1>, ren2 : UInt<1>, ren3 : UInt<1>, swap12 : UInt<1>, swap23 : UInt<1>, single : UInt<1>, fromint : UInt<1>, toint : UInt<1>, fastpipe : UInt<1>, fma : UInt<1>, div_wky : UInt<1>, sqrt : UInt<1>, wflags : UInt<1>}, sboard_set : UInt<1>, sboard_clr : UInt<1>, sboard_clra : UInt<5>},  flip rocc : { flip cmd : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {inst_wky : {funct : UInt<7>, rs2 : UInt<5>, rs1 : UInt<5>, xd : UInt<1>, xs1 : UInt<1>, xs2 : UInt<1>, rd : UInt<5>, opcode : UInt<7>}, rs1 : UInt<64>, rs2 : UInt<64>, status : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}}}, resp : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {rd : UInt<5>, data : UInt<64>}}, mem : {req : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {addr : UInt<40>, tag : UInt<7>, cmd : UInt<5>, typ : UInt<3>, phys : UInt<1>, data : UInt<64>}}, s1_kill : UInt<1>, s1_data : UInt<64>,  flip s2_nack : UInt<1>,  flip acquire : UInt<1>,  flip release : UInt<1>,  flip resp : {valid : UInt<1>, bits_wky : {addr : UInt<40>, tag : UInt<7>, cmd : UInt<5>, typ : UInt<3>, data : UInt<64>, replay : UInt<1>, has_data : UInt<1>, data_word_bypass : UInt<64>, store_data : UInt<64>}},  flip replay_next : UInt<1>,  flip xcpt : {ma : {ld : UInt<1>, st : UInt<1>}, pf : {ld : UInt<1>, st : UInt<1>}}, invalidate_lr : UInt<1>,  flip ordered : UInt<1>}, busy : UInt<1>, interrupt : UInt<1>,  flip exception : UInt<1>}}
    io is invalid
    io is invalid
    reg ex_ctrl : {legal : UInt<1>, fp : UInt<1>, rocc : UInt<1>, branch : UInt<1>, jal : UInt<1>, jalr : UInt<1>, rxs2 : UInt<1>, rxs1 : UInt<1>, sel_alu2 : UInt<2>, sel_alu1 : UInt<2>, sel_imm : UInt<3>, alu_dw : UInt<1>, alu_fn : UInt<4>, mem : UInt<1>, mem_cmd : UInt<5>, mem_type : UInt<3>, rfs1 : UInt<1>, rfs2 : UInt<1>, rfs3 : UInt<1>, wfd : UInt<1>, div_wky : UInt<1>, wxd : UInt<1>, csr : UInt<3>, fence_i : UInt<1>, fence : UInt<1>, amo : UInt<1>, dp : UInt<1>}, clock 
    reg mem_ctrl : {legal : UInt<1>, fp : UInt<1>, rocc : UInt<1>, branch : UInt<1>, jal : UInt<1>, jalr : UInt<1>, rxs2 : UInt<1>, rxs1 : UInt<1>, sel_alu2 : UInt<2>, sel_alu1 : UInt<2>, sel_imm : UInt<3>, alu_dw : UInt<1>, alu_fn : UInt<4>, mem : UInt<1>, mem_cmd : UInt<5>, mem_type : UInt<3>, rfs1 : UInt<1>, rfs2 : UInt<1>, rfs3 : UInt<1>, wfd : UInt<1>, div_wky : UInt<1>, wxd : UInt<1>, csr : UInt<3>, fence_i : UInt<1>, fence : UInt<1>, amo : UInt<1>, dp : UInt<1>}, clock 
    reg wb_ctrl : {legal : UInt<1>, fp : UInt<1>, rocc : UInt<1>, branch : UInt<1>, jal : UInt<1>, jalr : UInt<1>, rxs2 : UInt<1>, rxs1 : UInt<1>, sel_alu2 : UInt<2>, sel_alu1 : UInt<2>, sel_imm : UInt<3>, alu_dw : UInt<1>, alu_fn : UInt<4>, mem : UInt<1>, mem_cmd : UInt<5>, mem_type : UInt<3>, rfs1 : UInt<1>, rfs2 : UInt<1>, rfs3 : UInt<1>, wfd : UInt<1>, div_wky : UInt<1>, wxd : UInt<1>, csr : UInt<3>, fence_i : UInt<1>, fence : UInt<1>, amo : UInt<1>, dp : UInt<1>}, clock 
    reg ex_reg_xcpt_interrupt : UInt<1>, clock 
    reg ex_reg_valid : UInt<1>, clock 
    reg ex_reg_rvc : UInt<1>, clock 
    reg ex_reg_btb_hit : UInt<1>, clock 
    reg ex_reg_btb_resp : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}, clock 
    reg ex_reg_xcpt : UInt<1>, clock 
    reg ex_reg_flush_pipe : UInt<1>, clock 
    reg ex_reg_load_use : UInt<1>, clock 
    reg ex_cause : UInt<64>, clock 
    reg ex_reg_replay : UInt<1>, clock 
    reg ex_reg_pc : UInt<40>, clock 
    reg ex_reg_inst : UInt<32>, clock 
    reg mem_reg_xcpt_interrupt : UInt<1>, clock 
    reg mem_reg_valid : UInt<1>, clock 
    reg mem_reg_rvc : UInt<1>, clock 
    reg mem_reg_btb_hit : UInt<1>, clock 
    reg mem_reg_btb_resp : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}, clock 
    reg mem_reg_xcpt : UInt<1>, clock 
    reg mem_reg_replay : UInt<1>, clock 
    reg mem_reg_flush_pipe : UInt<1>, clock 
    reg mem_reg_cause : UInt<64>, clock 
    reg mem_reg_slow_bypass : UInt<1>, clock 
    reg mem_reg_load : UInt<1>, clock 
    reg mem_reg_store : UInt<1>, clock 
    reg mem_reg_pc : UInt<40>, clock 
    reg mem_reg_inst : UInt<32>, clock 
    reg mem_reg_wdata : UInt<64>, clock 
    reg mem_reg_rs2 : UInt<64>, clock 
    wire take_pc_mem : UInt<1>
    take_pc_mem is invalid
    reg wb_reg_valid : UInt<1>, clock 
    reg wb_reg_xcpt : UInt<1>, clock 
    reg wb_reg_replay : UInt<1>, clock 
    reg wb_reg_cause : UInt<64>, clock 
    reg wb_reg_pc : UInt<40>, clock 
    reg wb_reg_inst : UInt<32>, clock 
    reg wb_reg_wdata : UInt<64>, clock 
    reg wb_reg_rs2 : UInt<64>, clock 
    wire take_pc_wb : UInt<1>
    take_pc_wb is invalid
    wire take_pc_id : UInt<1>
    take_pc_id is invalid
    node take_pc_mem_wb = or(take_pc_wb, take_pc_mem)
    node take_pc = or(take_pc_mem_wb, take_pc_id)
    inst ibuf aof IBuf
    ibuf.io is invalid
    ibuf.clock <= clock
    ibuf.reset_wky <= reset_wky
    ibuf.io.imem <= io.imem.resp
    ibuf.io.kill <= take_pc
    wire id_ctrl : {legal : UInt<1>, fp : UInt<1>, rocc : UInt<1>, branch : UInt<1>, jal : UInt<1>, jalr : UInt<1>, rxs2 : UInt<1>, rxs1 : UInt<1>, sel_alu2 : UInt<2>, sel_alu1 : UInt<2>, sel_imm : UInt<3>, alu_dw : UInt<1>, alu_fn : UInt<4>, mem : UInt<1>, mem_cmd : UInt<5>, mem_type : UInt<3>, rfs1 : UInt<1>, rfs2 : UInt<1>, rfs3 : UInt<1>, wfd : UInt<1>, div_wky : UInt<1>, wxd : UInt<1>, csr : UInt<3>, fence_i : UInt<1>, fence : UInt<1>, amo : UInt<1>, dp : UInt<1>}
    id_ctrl is invalid
    node _T_2603 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8319))
    node _T_2605 = eq(_T_2603, UInt<32>(3))
    node _T_2607 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4207))
    node _T_2609 = eq(_T_2607, UInt<32>(3))
    node _T_2611 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24703))
    node _T_2613 = eq(_T_2611, UInt<32>(15))
    node _T_2615 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(28791))
    node _T_2617 = eq(_T_2615, UInt<32>(19))
    node _T_2619 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(95))
    node _T_2621 = eq(_T_2619, UInt<32>(23))
    node _T_2623 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4227858559))
    node _T_2625 = eq(_T_2623, UInt<32>(51))
    node _T_2627 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3187699831))
    node _T_2629 = eq(_T_2627, UInt<32>(51))
    node _T_2631 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(67108979))
    node _T_2633 = eq(_T_2631, UInt<32>(67))
    node _T_2635 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3825205375))
    node _T_2637 = eq(_T_2635, UInt<32>(83))
    node _T_2639 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(28795))
    node _T_2641 = eq(_T_2639, UInt<32>(99))
    node _T_2643 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(127))
    node _T_2645 = eq(_T_2643, UInt<32>(111))
    node _T_2647 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4293918719))
    node _T_2649 = eq(_T_2647, UInt<32>(115))
    node _T_2651 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4227870815))
    node _T_2653 = eq(_T_2651, UInt<32>(4115))
    node _T_2655 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4261425247))
    node _T_2657 = eq(_T_2655, UInt<32>(4123))
    node _T_2659 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24667))
    node _T_2661 = eq(_T_2659, UInt<32>(8195))
    node _T_2663 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8319))
    node _T_2665 = eq(_T_2663, UInt<32>(8211))
    node _T_2667 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(402677887))
    node _T_2669 = eq(_T_2667, UInt<32>(8239))
    node _T_2671 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8319))
    node _T_2673 = eq(_T_2671, UInt<32>(8307))
    node _T_2675 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3154145407))
    node _T_2677 = eq(_T_2675, UInt<32>(20499))
    node _T_2679 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3187699807))
    node _T_2681 = eq(_T_2679, UInt<32>(20507))
    node _T_2683 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3187699831))
    node _T_2685 = eq(_T_2683, UInt<32>(20531))
    node _T_2687 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4261429367))
    node _T_2689 = eq(_T_2687, UInt<32>(33570867))
    node _T_2691 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3892338815))
    node _T_2693 = eq(_T_2691, UInt<32>(134225967))
    node _T_2695 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4193280127))
    node _T_2697 = eq(_T_2695, UInt<32>(268443695))
    node _T_2699 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3758096383))
    node _T_2701 = eq(_T_2699, UInt<32>(270532723))
    node _T_2703 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(273678451))
    node _T_2705 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4261445631))
    node _T_2707 = eq(_T_2705, UInt<32>(301990003))
    node _T_2709 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4093665407))
    node _T_2711 = eq(_T_2709, UInt<32>(536870995))
    node _T_2713 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2080399487))
    node _T_2715 = eq(_T_2713, UInt<32>(536870995))
    node _T_2717 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2080395391))
    node _T_2719 = eq(_T_2717, UInt<32>(536870995))
    node _T_2721 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2146435199))
    node _T_2723 = eq(_T_2721, UInt<32>(1074790483))
    node _T_2725 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2146435199))
    node _T_2727 = eq(_T_2725, UInt<32>(1107296339))
    node _T_2729 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4260364415))
    node _T_2731 = eq(_T_2729, UInt<32>(1476395091))
    node _T_2733 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2065694835))
    node _T_2735 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3988783231))
    node _T_2737 = eq(_T_2735, UInt<32>(3221225555))
    node _T_2739 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4260388991))
    node _T_2741 = eq(_T_2739, UInt<32>(3758096467))
    node _T_2743 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3991957631))
    node _T_2745 = eq(_T_2743, UInt<32>(3758096467))
    node _T_2747 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24639))
    node _T_2749 = eq(_T_2747, UInt<32>(35))
    node _T_2751 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12399))
    node _T_2753 = eq(_T_2751, UInt<32>(4195))
    node _T_2755 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16511))
    node _T_2757 = eq(_T_2755, UInt<32>(16483))
    node _T_2759 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4227887223))
    node _T_2761 = eq(_T_2759, UInt<32>(51))
    node _T_2763 = or(UInt<1>(0), _T_2605)
    node _T_2764 = or(_T_2763, _T_2609)
    node _T_2765 = or(_T_2764, _T_2613)
    node _T_2766 = or(_T_2765, _T_2617)
    node _T_2767 = or(_T_2766, _T_2621)
    node _T_2768 = or(_T_2767, _T_2625)
    node _T_2769 = or(_T_2768, _T_2629)
    node _T_2770 = or(_T_2769, _T_2633)
    node _T_2771 = or(_T_2770, _T_2637)
    node _T_2772 = or(_T_2771, _T_2641)
    node _T_2773 = or(_T_2772, _T_2645)
    node _T_2774 = or(_T_2773, _T_2649)
    node _T_2775 = or(_T_2774, _T_2653)
    node _T_2776 = or(_T_2775, _T_2657)
    node _T_2777 = or(_T_2776, _T_2661)
    node _T_2778 = or(_T_2777, _T_2665)
    node _T_2779 = or(_T_2778, _T_2669)
    node _T_2780 = or(_T_2779, _T_2673)
    node _T_2781 = or(_T_2780, _T_2677)
    node _T_2782 = or(_T_2781, _T_2681)
    node _T_2783 = or(_T_2782, _T_2685)
    node _T_2784 = or(_T_2783, _T_2689)
    node _T_2785 = or(_T_2784, _T_2693)
    node _T_2786 = or(_T_2785, _T_2697)
    node _T_2787 = or(_T_2786, _T_2701)
    node _T_2788 = or(_T_2787, _T_2703)
    node _T_2789 = or(_T_2788, _T_2707)
    node _T_2790 = or(_T_2789, _T_2711)
    node _T_2791 = or(_T_2790, _T_2715)
    node _T_2792 = or(_T_2791, _T_2719)
    node _T_2793 = or(_T_2792, _T_2723)
    node _T_2794 = or(_T_2793, _T_2727)
    node _T_2795 = or(_T_2794, _T_2731)
    node _T_2796 = or(_T_2795, _T_2733)
    node _T_2797 = or(_T_2796, _T_2737)
    node _T_2798 = or(_T_2797, _T_2741)
    node _T_2799 = or(_T_2798, _T_2745)
    node _T_2800 = or(_T_2799, _T_2749)
    node _T_2801 = or(_T_2800, _T_2753)
    node _T_2802 = or(_T_2801, _T_2757)
    node _T_2803 = or(_T_2802, _T_2761)
    node _T_2805 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(92))
    node _T_2807 = eq(_T_2805, UInt<32>(4))
    node _T_2809 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(96))
    node _T_2811 = eq(_T_2809, UInt<32>(64))
    node _T_2813 = or(UInt<1>(0), _T_2807)
    node _T_2814 = or(_T_2813, _T_2811)
    node _T_2817 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(116))
    node _T_2819 = eq(_T_2817, UInt<32>(96))
    node _T_2821 = or(UInt<1>(0), _T_2819)
    node _T_2823 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(104))
    node _T_2825 = eq(_T_2823, UInt<32>(104))
    node _T_2827 = or(UInt<1>(0), _T_2825)
    node _T_2829 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8252))
    node _T_2831 = eq(_T_2829, UInt<32>(36))
    node _T_2833 = or(UInt<1>(0), _T_2831)
    node _T_2835 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(100))
    node _T_2837 = eq(_T_2835, UInt<32>(32))
    node _T_2839 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(52))
    node _T_2841 = eq(_T_2839, UInt<32>(32))
    node _T_2843 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8264))
    node _T_2845 = eq(_T_2843, UInt<32>(8200))
    node _T_2847 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1107308580))
    node _T_2849 = eq(_T_2847, UInt<32>(33554464))
    node _T_2851 = or(UInt<1>(0), _T_2837)
    node _T_2852 = or(_T_2851, _T_2841)
    node _T_2853 = or(_T_2852, _T_2845)
    node _T_2854 = or(_T_2853, _T_2849)
    node _T_2856 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(68))
    node _T_2858 = eq(_T_2856, UInt<32>(0))
    node _T_2860 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16420))
    node _T_2862 = eq(_T_2860, UInt<32>(32))
    node _T_2864 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(56))
    node _T_2866 = eq(_T_2864, UInt<32>(32))
    node _T_2868 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8272))
    node _T_2870 = eq(_T_2868, UInt<32>(8192))
    node _T_2872 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2415919156))
    node _T_2874 = eq(_T_2872, UInt<32>(2415919120))
    node _T_2876 = or(UInt<1>(0), _T_2858)
    node _T_2877 = or(_T_2876, _T_2862)
    node _T_2878 = or(_T_2877, _T_2866)
    node _T_2879 = or(_T_2878, _T_2870)
    node _T_2880 = or(_T_2879, _T_2874)
    node _T_2882 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(88))
    node _T_2884 = eq(_T_2882, UInt<32>(0))
    node _T_2886 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(32))
    node _T_2888 = eq(_T_2886, UInt<32>(0))
    node _T_2890 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12))
    node _T_2892 = eq(_T_2890, UInt<32>(4))
    node _T_2894 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(72))
    node _T_2896 = eq(_T_2894, UInt<32>(72))
    node _T_2898 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16464))
    node _T_2900 = eq(_T_2898, UInt<32>(16464))
    node _T_2902 = or(UInt<1>(0), _T_2884)
    node _T_2903 = or(_T_2902, _T_2888)
    node _T_2904 = or(_T_2903, _T_2892)
    node _T_2905 = or(_T_2904, _T_2896)
    node _T_2906 = or(_T_2905, _T_2900)
    node _T_2908 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(72))
    node _T_2910 = eq(_T_2908, UInt<32>(0))
    node _T_2912 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24))
    node _T_2914 = eq(_T_2912, UInt<32>(0))
    node _T_2916 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16392))
    node _T_2918 = eq(_T_2916, UInt<32>(16384))
    node _T_2920 = or(UInt<1>(0), _T_2910)
    node _T_2921 = or(_T_2920, _T_2858)
    node _T_2922 = or(_T_2921, _T_2914)
    node _T_2923 = or(_T_2922, _T_2918)
    node _T_2924 = cat(_T_2923, _T_2906)
    node _T_2926 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16388))
    node _T_2928 = eq(_T_2926, UInt<32>(0))
    node _T_2930 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(80))
    node _T_2932 = eq(_T_2930, UInt<32>(0))
    node _T_2934 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(36))
    node _T_2936 = eq(_T_2934, UInt<32>(0))
    node _T_2938 = or(UInt<1>(0), _T_2928)
    node _T_2939 = or(_T_2938, _T_2932)
    node _T_2940 = or(_T_2939, _T_2858)
    node _T_2941 = or(_T_2940, _T_2936)
    node _T_2942 = or(_T_2941, _T_2914)
    node _T_2944 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(52))
    node _T_2946 = eq(_T_2944, UInt<32>(20))
    node _T_2948 = or(UInt<1>(0), _T_2946)
    node _T_2949 = or(_T_2948, _T_2896)
    node _T_2950 = cat(_T_2949, _T_2942)
    node _T_2952 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24))
    node _T_2954 = eq(_T_2952, UInt<32>(8))
    node _T_2956 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(68))
    node _T_2958 = eq(_T_2956, UInt<32>(64))
    node _T_2960 = or(UInt<1>(0), _T_2954)
    node _T_2961 = or(_T_2960, _T_2958)
    node _T_2963 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(20))
    node _T_2965 = eq(_T_2963, UInt<32>(20))
    node _T_2967 = or(UInt<1>(0), _T_2954)
    node _T_2968 = or(_T_2967, _T_2965)
    node _T_2970 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(48))
    node _T_2972 = eq(_T_2970, UInt<32>(0))
    node _T_2974 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8220))
    node _T_2976 = eq(_T_2974, UInt<32>(4))
    node _T_2978 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(20))
    node _T_2980 = eq(_T_2978, UInt<32>(16))
    node _T_2982 = or(UInt<1>(0), _T_2972)
    node _T_2983 = or(_T_2982, _T_2976)
    node _T_2984 = or(_T_2983, _T_2980)
    node _T_2985 = cat(_T_2984, _T_2968)
    node _T_2986 = cat(_T_2985, _T_2961)
    node _T_2988 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16))
    node _T_2990 = eq(_T_2988, UInt<32>(0))
    node _T_2992 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8))
    node _T_2994 = eq(_T_2992, UInt<32>(0))
    node _T_2996 = or(UInt<1>(0), _T_2990)
    node _T_2997 = or(_T_2996, _T_2994)
    node _T_2999 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12372))
    node _T_3001 = eq(_T_2999, UInt<32>(4112))
    node _T_3003 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4184))
    node _T_3005 = eq(_T_3003, UInt<32>(4160))
    node _T_3007 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(28740))
    node _T_3009 = eq(_T_3007, UInt<32>(28672))
    node _T_3011 = or(UInt<1>(0), _T_3001)
    node _T_3012 = or(_T_3011, _T_3005)
    node _T_3013 = or(_T_3012, _T_3009)
    node _T_3015 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16468))
    node _T_3017 = eq(_T_3015, UInt<32>(64))
    node _T_3019 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8280))
    node _T_3021 = eq(_T_3019, UInt<32>(8256))
    node _T_3023 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12372))
    node _T_3025 = eq(_T_3023, UInt<32>(12304))
    node _T_3027 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24660))
    node _T_3029 = eq(_T_3027, UInt<32>(24592))
    node _T_3031 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073754164))
    node _T_3033 = eq(_T_3031, UInt<32>(1073741872))
    node _T_3035 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073746004))
    node _T_3037 = eq(_T_3035, UInt<32>(1073745936))
    node _T_3039 = or(UInt<1>(0), _T_3017)
    node _T_3040 = or(_T_3039, _T_3021)
    node _T_3041 = or(_T_3040, _T_3025)
    node _T_3042 = or(_T_3041, _T_3029)
    node _T_3043 = or(_T_3042, _T_3033)
    node _T_3044 = or(_T_3043, _T_3037)
    node _T_3046 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8276))
    node _T_3048 = eq(_T_3046, UInt<32>(8208))
    node _T_3050 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073758292))
    node _T_3052 = eq(_T_3050, UInt<32>(16400))
    node _T_3054 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(20564))
    node _T_3056 = eq(_T_3054, UInt<32>(16400))
    node _T_3058 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16472))
    node _T_3060 = eq(_T_3058, UInt<32>(16448))
    node _T_3062 = or(UInt<1>(0), _T_3048)
    node _T_3063 = or(_T_3062, _T_3052)
    node _T_3064 = or(_T_3063, _T_3056)
    node _T_3065 = or(_T_3064, _T_3060)
    node _T_3067 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24660))
    node _T_3069 = eq(_T_3067, UInt<32>(8208))
    node _T_3071 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073754196))
    node _T_3073 = eq(_T_3071, UInt<32>(1073745936))
    node _T_3075 = or(UInt<1>(0), _T_3069)
    node _T_3076 = or(_T_3075, _T_3060)
    node _T_3077 = or(_T_3076, _T_3033)
    node _T_3078 = or(_T_3077, _T_3073)
    node _T_3079 = cat(_T_3044, _T_3013)
    node _T_3080 = cat(_T_3078, _T_3065)
    node _T_3081 = cat(_T_3080, _T_3079)
    node _T_3083 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16479))
    node _T_3085 = eq(_T_3083, UInt<32>(3))
    node _T_3087 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4223))
    node _T_3089 = eq(_T_3087, UInt<32>(3))
    node _T_3091 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(28799))
    node _T_3093 = eq(_T_3091, UInt<32>(4111))
    node _T_3095 = or(UInt<1>(0), _T_3085)
    node _T_3096 = or(_T_3095, _T_2605)
    node _T_3097 = or(_T_3096, _T_3089)
    node _T_3098 = or(_T_3097, _T_3093)
    node _T_3099 = or(_T_3098, _T_2661)
    node _T_3100 = or(_T_3099, _T_2669)
    node _T_3101 = or(_T_3100, _T_2693)
    node _T_3102 = or(_T_3101, _T_2697)
    node _T_3104 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8200))
    node _T_3106 = eq(_T_3104, UInt<32>(8))
    node _T_3108 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(40))
    node _T_3110 = eq(_T_3108, UInt<32>(32))
    node _T_3112 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(402653216))
    node _T_3114 = eq(_T_3112, UInt<32>(402653216))
    node _T_3116 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(536870944))
    node _T_3118 = eq(_T_3116, UInt<32>(536870944))
    node _T_3120 = or(UInt<1>(0), _T_3106)
    node _T_3121 = or(_T_3120, _T_3110)
    node _T_3122 = or(_T_3121, _T_3114)
    node _T_3123 = or(_T_3122, _T_3118)
    node _T_3125 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(268443656))
    node _T_3127 = eq(_T_3125, UInt<32>(268443656))
    node _T_3129 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073750024))
    node _T_3131 = eq(_T_3129, UInt<32>(1073750024))
    node _T_3133 = or(UInt<1>(0), _T_3127)
    node _T_3134 = or(_T_3133, _T_3131)
    node _T_3136 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(134217736))
    node _T_3138 = eq(_T_3136, UInt<32>(134217736))
    node _T_3140 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(268435464))
    node _T_3142 = eq(_T_3140, UInt<32>(268435464))
    node _T_3144 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2147483656))
    node _T_3146 = eq(_T_3144, UInt<32>(2147483656))
    node _T_3148 = or(UInt<1>(0), _T_3106)
    node _T_3149 = or(_T_3148, _T_3138)
    node _T_3150 = or(_T_3149, _T_3142)
    node _T_3151 = or(_T_3150, _T_3146)
    node _T_3153 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(402661384))
    node _T_3155 = eq(_T_3153, UInt<32>(8200))
    node _T_3157 = or(UInt<1>(0), _T_3155)
    node _T_3159 = cat(_T_3134, _T_3123)
    node _T_3160 = cat(UInt<1>(0), _T_3157)
    node _T_3161 = cat(_T_3160, _T_3151)
    node _T_3162 = cat(_T_3161, _T_3159)
    node _T_3164 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4096))
    node _T_3166 = eq(_T_3164, UInt<32>(4096))
    node _T_3168 = or(UInt<1>(0), _T_3166)
    node _T_3170 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8192))
    node _T_3172 = eq(_T_3170, UInt<32>(8192))
    node _T_3174 = or(UInt<1>(0), _T_3172)
    node _T_3176 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(16384))
    node _T_3178 = eq(_T_3176, UInt<32>(16384))
    node _T_3180 = or(UInt<1>(0), _T_3178)
    node _T_3181 = cat(_T_3180, _T_3174)
    node _T_3182 = cat(_T_3181, _T_3168)
    node _T_3184 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2147483744))
    node _T_3186 = eq(_T_3184, UInt<32>(64))
    node _T_3188 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(268435552))
    node _T_3190 = eq(_T_3188, UInt<32>(64))
    node _T_3192 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(112))
    node _T_3194 = eq(_T_3192, UInt<32>(64))
    node _T_3196 = or(UInt<1>(0), _T_3186)
    node _T_3197 = or(_T_3196, _T_3190)
    node _T_3198 = or(_T_3197, _T_3194)
    node _T_3200 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(124))
    node _T_3202 = eq(_T_3200, UInt<32>(36))
    node _T_3204 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(1073741920))
    node _T_3206 = eq(_T_3204, UInt<32>(64))
    node _T_3208 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2415919200))
    node _T_3210 = eq(_T_3208, UInt<32>(268435520))
    node _T_3212 = or(UInt<1>(0), _T_3202)
    node _T_3213 = or(_T_3212, _T_3206)
    node _T_3214 = or(_T_3213, _T_3194)
    node _T_3215 = or(_T_3214, _T_3210)
    node _T_3217 = or(UInt<1>(0), _T_3194)
    node _T_3219 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(60))
    node _T_3221 = eq(_T_3219, UInt<32>(4))
    node _T_3223 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(268435552))
    node _T_3225 = eq(_T_3223, UInt<32>(268435520))
    node _T_3227 = or(UInt<1>(0), _T_3221)
    node _T_3228 = or(_T_3227, _T_3186)
    node _T_3229 = or(_T_3228, _T_3194)
    node _T_3230 = or(_T_3229, _T_3225)
    node _T_3232 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(33554548))
    node _T_3234 = eq(_T_3232, UInt<32>(33554480))
    node _T_3236 = or(UInt<1>(0), _T_3234)
    node _T_3238 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(100))
    node _T_3240 = eq(_T_3238, UInt<32>(0))
    node _T_3242 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(80))
    node _T_3244 = eq(_T_3242, UInt<32>(16))
    node _T_3246 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8228))
    node _T_3248 = eq(_T_3246, UInt<32>(36))
    node _T_3250 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(40))
    node _T_3252 = eq(_T_3250, UInt<32>(40))
    node _T_3254 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4144))
    node _T_3256 = eq(_T_3254, UInt<32>(4144))
    node _T_3258 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8240))
    node _T_3260 = eq(_T_3258, UInt<32>(8240))
    node _T_3262 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(2415919120))
    node _T_3264 = eq(_T_3262, UInt<32>(2147483664))
    node _T_3266 = or(UInt<1>(0), _T_3240)
    node _T_3267 = or(_T_3266, _T_3244)
    node _T_3268 = or(_T_3267, _T_3248)
    node _T_3269 = or(_T_3268, _T_3252)
    node _T_3270 = or(_T_3269, _T_3256)
    node _T_3271 = or(_T_3270, _T_3260)
    node _T_3272 = or(_T_3271, _T_3264)
    node _T_3274 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4208))
    node _T_3276 = eq(_T_3274, UInt<32>(4208))
    node _T_3278 = or(UInt<1>(0), _T_3276)
    node _T_3280 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(8304))
    node _T_3282 = eq(_T_3280, UInt<32>(8304))
    node _T_3284 = or(UInt<1>(0), _T_3282)
    node _T_3286 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12400))
    node _T_3288 = eq(_T_3286, UInt<32>(112))
    node _T_3290 = or(UInt<1>(0), _T_3288)
    node _T_3291 = cat(_T_3290, _T_3284)
    node _T_3292 = cat(_T_3291, _T_3278)
    node _T_3294 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12376))
    node _T_3296 = eq(_T_3294, UInt<32>(4104))
    node _T_3298 = or(UInt<1>(0), _T_3296)
    node _T_3300 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(12376))
    node _T_3302 = eq(_T_3300, UInt<32>(8))
    node _T_3304 = or(UInt<1>(0), _T_3302)
    node _T_3306 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(24648))
    node _T_3308 = eq(_T_3306, UInt<32>(8200))
    node _T_3310 = or(UInt<1>(0), _T_3308)
    node _T_3312 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(4188))
    node _T_3314 = eq(_T_3312, UInt<32>(4100))
    node _T_3316 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(33554528))
    node _T_3318 = eq(_T_3316, UInt<32>(33554496))
    node _T_3320 = and(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, UInt<32>(3489661040))
    node _T_3322 = eq(_T_3320, UInt<32>(1073741904))
    node _T_3324 = or(UInt<1>(0), _T_3314)
    node _T_3325 = or(_T_3324, _T_3318)
    node _T_3326 = or(_T_3325, _T_3322)
    id_ctrl.legal <= _T_2803
    id_ctrl.fp <= _T_2814
    id_ctrl.rocc <= UInt<1>(0)
    id_ctrl.branch <= _T_2821
    id_ctrl.jal <= _T_2827
    id_ctrl.jalr <= _T_2833
    id_ctrl.rxs2 <= _T_2854
    id_ctrl.rxs1 <= _T_2880
    id_ctrl.sel_alu2 <= _T_2924
    id_ctrl.sel_alu1 <= _T_2950
    id_ctrl.sel_imm <= _T_2986
    id_ctrl.alu_dw <= _T_2997
    id_ctrl.alu_fn <= _T_3081
    id_ctrl.mem <= _T_3102
    id_ctrl.mem_cmd <= _T_3162
    id_ctrl.mem_type <= _T_3182
    id_ctrl.rfs1 <= _T_3198
    id_ctrl.rfs2 <= _T_3215
    id_ctrl.rfs3 <= _T_3217
    id_ctrl.wfd <= _T_3230
    id_ctrl.div_wky <= _T_3236
    id_ctrl.wxd <= _T_3272
    id_ctrl.csr <= _T_3292
    id_ctrl.fence_i <= _T_3298
    id_ctrl.fence <= _T_3304
    id_ctrl.amo <= _T_3310
    id_ctrl.dp <= _T_3326
    wire id_load_use : UInt<1>
    id_load_use is invalid
    regreset id_reg_fence : UInt<1>, clock, reset_wky, UInt<1>(0)
    wire _T_3331 : UInt<64>[31]
    wire id_rs_0 : UInt<64>
    id_rs_0 is invalid
    node _T_3335 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, UInt<1>(0))
    node _T_3336 = and(UInt<1>(0), _T_3335)
    node _T_3338 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, 4, 0)
    node _T_3339 = not(_T_3338)
    node _T_3340 = _T_3331[_T_3339]
    node _T_3341 = mux(_T_3336, UInt<1>(0), _T_3340)
    id_rs_0 <= _T_3341
    wire id_rs_1 : UInt<64>
    id_rs_1 is invalid
    node _T_3345 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, UInt<1>(0))
    node _T_3346 = and(UInt<1>(0), _T_3345)
    node _T_3348 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, 4, 0)
    node _T_3349 = not(_T_3348)
    node _T_3350 = _T_3331[_T_3349]
    node _T_3351 = mux(_T_3346, UInt<1>(0), _T_3350)
    id_rs_1 <= _T_3351
    wire ctrl_killd : UInt<1>
    ctrl_killd is invalid
    node _T_3353 = asSInt(ibuf.io.pc)
    node _T_3356 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3358 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 31, 31)
    node _T_3359 = asSInt(_T_3358)
    node _T_3360 = mux(_T_3356, asSInt(UInt<1>(0)), _T_3359)
    node _T_3362 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3363 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 30, 20)
    node _T_3364 = asSInt(_T_3363)
    node _T_3365 = mux(_T_3362, _T_3364, _T_3360)
    node _T_3367 = neq(UInt<3>(3), UInt<3>(2))
    node _T_3369 = neq(UInt<3>(3), UInt<3>(3))
    node _T_3370 = and(_T_3367, _T_3369)
    node _T_3371 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 19, 12)
    node _T_3372 = asSInt(_T_3371)
    node _T_3373 = mux(_T_3370, _T_3360, _T_3372)
    node _T_3375 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3377 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3378 = or(_T_3375, _T_3377)
    node _T_3381 = eq(UInt<3>(3), UInt<3>(3))
    node _T_3382 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 20, 20)
    node _T_3383 = asSInt(_T_3382)
    node _T_3385 = eq(UInt<3>(3), UInt<3>(1))
    node _T_3386 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 7, 7)
    node _T_3387 = asSInt(_T_3386)
    node _T_3388 = mux(_T_3385, _T_3387, _T_3360)
    node _T_3389 = mux(_T_3381, _T_3383, _T_3388)
    node _T_3390 = mux(_T_3378, asSInt(UInt<1>(0)), _T_3389)
    node _T_3392 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3394 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3395 = or(_T_3392, _T_3394)
    node _T_3397 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 30, 25)
    node _T_3398 = mux(_T_3395, UInt<1>(0), _T_3397)
    node _T_3400 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3403 = eq(UInt<3>(3), UInt<3>(0))
    node _T_3405 = eq(UInt<3>(3), UInt<3>(1))
    node _T_3406 = or(_T_3403, _T_3405)
    node _T_3407 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 11, 8)
    node _T_3409 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3410 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 19, 16)
    node _T_3411 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 24, 21)
    node _T_3412 = mux(_T_3409, _T_3410, _T_3411)
    node _T_3413 = mux(_T_3406, _T_3407, _T_3412)
    node _T_3414 = mux(_T_3400, UInt<1>(0), _T_3413)
    node _T_3416 = eq(UInt<3>(3), UInt<3>(0))
    node _T_3417 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 7, 7)
    node _T_3419 = eq(UInt<3>(3), UInt<3>(4))
    node _T_3420 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 20, 20)
    node _T_3422 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3423 = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 15, 15)
    node _T_3425 = mux(_T_3422, _T_3423, UInt<1>(0))
    node _T_3426 = mux(_T_3419, _T_3420, _T_3425)
    node _T_3427 = mux(_T_3416, _T_3417, _T_3426)
    node _T_3428 = cat(_T_3398, _T_3414)
    node _T_3429 = cat(_T_3428, _T_3427)
    node _T_3430 = asUInt(_T_3390)
    node _T_3431 = asUInt(_T_3373)
    node _T_3432 = cat(_T_3431, _T_3430)
    node _T_3433 = asUInt(_T_3365)
    node _T_3434 = asUInt(_T_3360)
    node _T_3435 = cat(_T_3434, _T_3433)
    node _T_3436 = cat(_T_3435, _T_3432)
    node _T_3437 = cat(_T_3436, _T_3429)
    node _T_3438 = asSInt(_T_3437)
    node _T_3439 = add(_T_3353, _T_3438)
    node _T_3440 = tail(_T_3439, 1)
    node _T_3441 = asSInt(_T_3440)
    node id_npc = asUInt(_T_3441)
    node _T_3444 = eq(ctrl_killd, UInt<1>(0))
    node _T_3445 = and(UInt<1>(0), _T_3444)
    node _T_3446 = and(_T_3445, id_ctrl.jal)
    take_pc_id <= _T_3446
    inst csr aof CSRFile
    csr.io is invalid
    csr.clock <= clock
    csr.reset_wky <= reset_wky
    node _T_3450 = eq(id_ctrl.csr, UInt<3>(2))
    node _T_3451 = eq(id_ctrl.csr, UInt<3>(3))
    node _T_3452 = eq(id_ctrl.csr, UInt<3>(1))
    node _T_3453 = or(_T_3450, _T_3451)
    node id_csr_en = or(_T_3453, _T_3452)
    node id_system_insn = geq(id_ctrl.csr, UInt<3>(4))
    node _T_3457 = eq(id_ctrl.csr, UInt<3>(2))
    node _T_3458 = eq(id_ctrl.csr, UInt<3>(3))
    node _T_3459 = or(_T_3457, _T_3458)
    node _T_3461 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, UInt<1>(0))
    node id_csr_ren = and(_T_3459, _T_3461)
    node id_csr = mux(id_csr_ren, UInt<3>(5), id_ctrl.csr)
    node _T_3464 = eq(id_csr_ren, UInt<1>(0))
    node _T_3465 = and(id_csr_en, _T_3464)
    node _T_3466 = and(_T_3465, csr.io.decode.write_flush)
    node id_csr_flush = or(id_system_insn, _T_3466)
    node _T_3468 = eq(id_ctrl.legal, UInt<1>(0))
    node _T_3469 = bits(csr.io.status.isa, 12, 12)
    node _T_3471 = eq(_T_3469, UInt<1>(0))
    node _T_3472 = and(id_ctrl.div_wky, _T_3471)
    node _T_3473 = or(_T_3468, _T_3472)
    node _T_3474 = bits(csr.io.status.isa, 0, 0)
    node _T_3476 = eq(_T_3474, UInt<1>(0))
    node _T_3477 = and(id_ctrl.amo, _T_3476)
    node _T_3478 = or(_T_3473, _T_3477)
    node _T_3479 = or(csr.io.decode.fp_illegal, io.fpu.illegal_rm)
    node _T_3480 = and(id_ctrl.fp, _T_3479)
    node _T_3481 = or(_T_3478, _T_3480)
    node _T_3482 = bits(csr.io.status.isa, 3, 3)
    node _T_3484 = eq(_T_3482, UInt<1>(0))
    node _T_3485 = and(id_ctrl.dp, _T_3484)
    node _T_3486 = or(_T_3481, _T_3485)
    node _T_3487 = bits(csr.io.status.isa, 2, 2)
    node _T_3489 = eq(_T_3487, UInt<1>(0))
    node _T_3490 = and(ibuf.io.inst_wky[0].bits_wky.rvc, _T_3489)
    node _T_3491 = or(_T_3486, _T_3490)
    node _T_3492 = and(id_ctrl.rocc, csr.io.decode.rocc_illegal)
    node _T_3493 = or(_T_3491, _T_3492)
    node _T_3495 = eq(id_csr_ren, UInt<1>(0))
    node _T_3496 = and(_T_3495, csr.io.decode.write_illegal)
    node _T_3497 = or(csr.io.decode.read_illegal, _T_3496)
    node _T_3498 = and(id_csr_en, _T_3497)
    node _T_3499 = or(_T_3493, _T_3498)
    node _T_3500 = and(id_system_insn, csr.io.decode.system_illegal)
    node id_illegal_insn = or(_T_3499, _T_3500)
    node id_amo_aq = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 26, 26)
    node id_amo_rl = bits(ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky, 25, 25)
    node _T_3501 = and(id_ctrl.amo, id_amo_rl)
    node id_fence_next = or(id_ctrl.fence, _T_3501)
    node _T_3503 = eq(io.dmem.ordered, UInt<1>(0))
    node id_mem_busy = or(_T_3503, io.dmem.req.valid)
    node _T_3505 = and(ex_reg_valid, ex_ctrl.rocc)
    node _T_3506 = or(io.rocc.busy, _T_3505)
    node _T_3507 = and(mem_reg_valid, mem_ctrl.rocc)
    node _T_3508 = or(_T_3506, _T_3507)
    node _T_3509 = and(wb_reg_valid, wb_ctrl.rocc)
    node _T_3510 = or(_T_3508, _T_3509)
    node id_rocc_busy = and(UInt<1>(0), _T_3510)
    node _T_3511 = and(id_reg_fence, id_mem_busy)
    node _T_3512 = or(id_fence_next, _T_3511)
    id_reg_fence <= _T_3512
    node _T_3513 = and(id_rocc_busy, id_ctrl.fence)
    node _T_3514 = and(id_ctrl.amo, id_amo_aq)
    node _T_3515 = or(_T_3514, id_ctrl.fence_i)
    node _T_3516 = or(id_ctrl.mem, id_ctrl.rocc)
    node _T_3517 = and(id_reg_fence, _T_3516)
    node _T_3518 = or(_T_3515, _T_3517)
    node _T_3519 = and(id_mem_busy, _T_3518)
    node id_do_fence = or(_T_3513, _T_3519)
    inst bpu aof BreakpointUnit
    bpu.io is invalid
    bpu.clock <= clock
    bpu.reset_wky <= reset_wky
    bpu.io.status <= csr.io.status
    bpu.io.bp <= csr.io.bp
    bpu.io.pc <= ibuf.io.pc
    bpu.io.ea <= mem_reg_wdata
    node id_xcpt_if = or(ibuf.io.inst_wky[0].bits_wky.pf0, ibuf.io.inst_wky[0].bits_wky.pf1)
    node _T_3552 = or(csr.io.interrupt, bpu.io.debug_if)
    node _T_3553 = or(_T_3552, bpu.io.xcpt_if)
    node _T_3554 = or(_T_3553, id_xcpt_if)
    node id_xcpt = or(_T_3554, id_illegal_insn)
    node _T_3555 = mux(id_xcpt_if, UInt<1>(1), UInt<2>(2))
    node _T_3556 = mux(bpu.io.xcpt_if, UInt<2>(3), _T_3555)
    node _T_3557 = mux(bpu.io.debug_if, UInt<4>(13), _T_3556)
    node id_cause = mux(csr.io.interrupt, csr.io.interrupt_cause, _T_3557)
    node ex_waddr = bits(ex_reg_inst, 11, 7)
    node mem_waddr = bits(mem_reg_inst, 11, 7)
    node wb_waddr = bits(wb_reg_inst, 11, 7)
    node _T_3561 = and(ex_reg_valid, ex_ctrl.wxd)
    node _T_3562 = and(mem_reg_valid, mem_ctrl.wxd)
    node _T_3564 = eq(mem_ctrl.mem, UInt<1>(0))
    node _T_3565 = and(_T_3562, _T_3564)
    node _T_3566 = and(mem_reg_valid, mem_ctrl.wxd)
    node _T_3567 = eq(UInt<1>(0), ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node id_bypass_src_0_0 = and(UInt<1>(1), _T_3567)
    node _T_3568 = eq(ex_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node id_bypass_src_0_1 = and(_T_3561, _T_3568)
    node _T_3569 = eq(mem_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node id_bypass_src_0_2 = and(_T_3565, _T_3569)
    node _T_3570 = eq(mem_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node id_bypass_src_0_3 = and(_T_3566, _T_3570)
    node _T_3571 = eq(UInt<1>(0), ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node id_bypass_src_1_0 = and(UInt<1>(1), _T_3571)
    node _T_3572 = eq(ex_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node id_bypass_src_1_1 = and(_T_3561, _T_3572)
    node _T_3573 = eq(mem_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node id_bypass_src_1_2 = and(_T_3565, _T_3573)
    node _T_3574 = eq(mem_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node id_bypass_src_1_3 = and(_T_3566, _T_3574)
    wire bypass_mux : UInt<64>[4]
    bypass_mux is invalid
    bypass_mux[0] <= UInt<1>(0)
    bypass_mux[1] <= mem_reg_wdata
    bypass_mux[2] <= wb_reg_wdata
    bypass_mux[3] <= io.dmem.resp.bits_wky.data_word_bypass
    reg ex_reg_rs_bypass : UInt<1>[2], clock 
    reg ex_reg_rs_lsb : UInt<2>[2], clock 
    reg ex_reg_rs_msb : UInt<62>[2], clock 
    node _T_3605 = cat(ex_reg_rs_msb[0], ex_reg_rs_lsb[0])
    node ex_rs_0 = mux(ex_reg_rs_bypass[0], bypass_mux[ex_reg_rs_lsb[0]], _T_3605)
    node _T_3607 = cat(ex_reg_rs_msb[1], ex_reg_rs_lsb[1])
    node ex_rs_1 = mux(ex_reg_rs_bypass[1], bypass_mux[ex_reg_rs_lsb[1]], _T_3607)
    node _T_3609 = eq(ex_ctrl.sel_imm, UInt<3>(5))
    node _T_3611 = bits(ex_reg_inst, 31, 31)
    node _T_3612 = asSInt(_T_3611)
    node _T_3613 = mux(_T_3609, asSInt(UInt<1>(0)), _T_3612)
    node _T_3615 = eq(ex_ctrl.sel_imm, UInt<3>(2))
    node _T_3616 = bits(ex_reg_inst, 30, 20)
    node _T_3617 = asSInt(_T_3616)
    node _T_3618 = mux(_T_3615, _T_3617, _T_3613)
    node _T_3620 = neq(ex_ctrl.sel_imm, UInt<3>(2))
    node _T_3622 = neq(ex_ctrl.sel_imm, UInt<3>(3))
    node _T_3623 = and(_T_3620, _T_3622)
    node _T_3624 = bits(ex_reg_inst, 19, 12)
    node _T_3625 = asSInt(_T_3624)
    node _T_3626 = mux(_T_3623, _T_3613, _T_3625)
    node _T_3628 = eq(ex_ctrl.sel_imm, UInt<3>(2))
    node _T_3630 = eq(ex_ctrl.sel_imm, UInt<3>(5))
    node _T_3631 = or(_T_3628, _T_3630)
    node _T_3634 = eq(ex_ctrl.sel_imm, UInt<3>(3))
    node _T_3635 = bits(ex_reg_inst, 20, 20)
    node _T_3636 = asSInt(_T_3635)
    node _T_3638 = eq(ex_ctrl.sel_imm, UInt<3>(1))
    node _T_3639 = bits(ex_reg_inst, 7, 7)
    node _T_3640 = asSInt(_T_3639)
    node _T_3641 = mux(_T_3638, _T_3640, _T_3613)
    node _T_3642 = mux(_T_3634, _T_3636, _T_3641)
    node _T_3643 = mux(_T_3631, asSInt(UInt<1>(0)), _T_3642)
    node _T_3645 = eq(ex_ctrl.sel_imm, UInt<3>(2))
    node _T_3647 = eq(ex_ctrl.sel_imm, UInt<3>(5))
    node _T_3648 = or(_T_3645, _T_3647)
    node _T_3650 = bits(ex_reg_inst, 30, 25)
    node _T_3651 = mux(_T_3648, UInt<1>(0), _T_3650)
    node _T_3653 = eq(ex_ctrl.sel_imm, UInt<3>(2))
    node _T_3656 = eq(ex_ctrl.sel_imm, UInt<3>(0))
    node _T_3658 = eq(ex_ctrl.sel_imm, UInt<3>(1))
    node _T_3659 = or(_T_3656, _T_3658)
    node _T_3660 = bits(ex_reg_inst, 11, 8)
    node _T_3662 = eq(ex_ctrl.sel_imm, UInt<3>(5))
    node _T_3663 = bits(ex_reg_inst, 19, 16)
    node _T_3664 = bits(ex_reg_inst, 24, 21)
    node _T_3665 = mux(_T_3662, _T_3663, _T_3664)
    node _T_3666 = mux(_T_3659, _T_3660, _T_3665)
    node _T_3667 = mux(_T_3653, UInt<1>(0), _T_3666)
    node _T_3669 = eq(ex_ctrl.sel_imm, UInt<3>(0))
    node _T_3670 = bits(ex_reg_inst, 7, 7)
    node _T_3672 = eq(ex_ctrl.sel_imm, UInt<3>(4))
    node _T_3673 = bits(ex_reg_inst, 20, 20)
    node _T_3675 = eq(ex_ctrl.sel_imm, UInt<3>(5))
    node _T_3676 = bits(ex_reg_inst, 15, 15)
    node _T_3678 = mux(_T_3675, _T_3676, UInt<1>(0))
    node _T_3679 = mux(_T_3672, _T_3673, _T_3678)
    node _T_3680 = mux(_T_3669, _T_3670, _T_3679)
    node _T_3681 = cat(_T_3651, _T_3667)
    node _T_3682 = cat(_T_3681, _T_3680)
    node _T_3683 = asUInt(_T_3643)
    node _T_3684 = asUInt(_T_3626)
    node _T_3685 = cat(_T_3684, _T_3683)
    node _T_3686 = asUInt(_T_3618)
    node _T_3687 = asUInt(_T_3613)
    node _T_3688 = cat(_T_3687, _T_3686)
    node _T_3689 = cat(_T_3688, _T_3685)
    node _T_3690 = cat(_T_3689, _T_3682)
    node ex_imm = asSInt(_T_3690)
    node _T_3693 = asSInt(ex_rs_0)
    node _T_3695 = asSInt(ex_reg_pc)
    node _T_3696 = eq(UInt<2>(2), ex_ctrl.sel_alu1)
    node _T_3697 = mux(_T_3696, _T_3695, asSInt(UInt<1>(0)))
    node _T_3698 = eq(UInt<2>(1), ex_ctrl.sel_alu1)
    node ex_op1 = mux(_T_3698, _T_3693, _T_3697)
    node _T_3701 = asSInt(ex_rs_1)
    node _T_3706 = mux(ex_reg_rvc, asSInt(UInt<3>(2)), asSInt(UInt<4>(4)))
    node _T_3707 = eq(UInt<2>(1), ex_ctrl.sel_alu2)
    node _T_3708 = mux(_T_3707, _T_3706, asSInt(UInt<1>(0)))
    node _T_3709 = eq(UInt<2>(3), ex_ctrl.sel_alu2)
    node _T_3710 = mux(_T_3709, ex_imm, _T_3708)
    node _T_3711 = eq(UInt<2>(2), ex_ctrl.sel_alu2)
    node ex_op2 = mux(_T_3711, _T_3701, _T_3710)
    inst alu aof ALU
    alu.io is invalid
    alu.clock <= clock
    alu.reset_wky <= reset_wky
    alu.io.dw <= ex_ctrl.alu_dw
    alu.io.fn <= ex_ctrl.alu_fn
    node _T_3712 = asUInt(ex_op2)
    alu.io.in2 <= _T_3712
    node _T_3713 = asUInt(ex_op1)
    alu.io.in1 <= _T_3713
    inst div_wky aof MulDiv
    div_wky.io is invalid
    div_wky.clock <= clock
    div_wky.reset_wky <= reset_wky
    node _T_3714 = and(ex_reg_valid, ex_ctrl.div_wky)
    div_wky.io.req.valid <= _T_3714
    div_wky.io.req.bits_wky.dw <= ex_ctrl.alu_dw
    div_wky.io.req.bits_wky.fn <= ex_ctrl.alu_fn
    div_wky.io.req.bits_wky.in1 <= ex_rs_0
    div_wky.io.req.bits_wky.in2 <= ex_rs_1
    div_wky.io.req.bits_wky.tag <= ex_waddr
    node _T_3716 = eq(ctrl_killd, UInt<1>(0))
    ex_reg_valid <= _T_3716
    node _T_3718 = eq(take_pc, UInt<1>(0))
    node _T_3719 = and(_T_3718, ibuf.io.inst_wky[0].valid)
    node _T_3720 = and(_T_3719, ibuf.io.inst_wky[0].bits_wky.replay)
    ex_reg_replay <= _T_3720
    node _T_3722 = eq(ctrl_killd, UInt<1>(0))
    node _T_3723 = and(_T_3722, id_xcpt)
    ex_reg_xcpt <= _T_3723
    node _T_3725 = eq(take_pc, UInt<1>(0))
    node _T_3726 = and(_T_3725, ibuf.io.inst_wky[0].valid)
    node _T_3727 = and(_T_3726, csr.io.interrupt)
    ex_reg_xcpt_interrupt <= _T_3727
    when id_xcpt : 
{
      ex_cause <= id_cause
      skip
}
    ex_reg_btb_hit <= ibuf.io.inst_wky[0].bits_wky.btb_hit
    when ibuf.io.inst_wky[0].bits_wky.btb_hit : 
{
      ex_reg_btb_resp <= ibuf.io.btb_resp
      skip
}
    node _T_3729 = eq(ctrl_killd, UInt<1>(0))
    when _T_3729 : 
{
      ex_ctrl <= id_ctrl
      ex_reg_rvc <= ibuf.io.inst_wky[0].bits_wky.rvc
      ex_ctrl.csr <= id_csr
      when id_xcpt : 
{
        ex_ctrl.alu_fn <= UInt<1>(0)
        ex_ctrl.alu_dw <= UInt<1>(1)
        ex_ctrl.sel_alu1 <= UInt<2>(2)
        ex_ctrl.sel_alu2 <= UInt<2>(0)
        node _T_3735 = eq(bpu.io.xcpt_if, UInt<1>(0))
        node _T_3737 = eq(ibuf.io.inst_wky[0].bits_wky.pf0, UInt<1>(0))
        node _T_3738 = and(_T_3735, _T_3737)
        node _T_3739 = and(_T_3738, ibuf.io.inst_wky[0].bits_wky.pf1)
        when _T_3739 : 
{
          ex_ctrl.sel_alu2 <= UInt<2>(1)
          ex_reg_rvc <= UInt<1>(1)
          skip
}
        skip
}
      node _T_3742 = or(id_ctrl.fence_i, id_csr_flush)
      node _T_3743 = or(_T_3742, csr.io.singleStep)
      ex_reg_flush_pipe <= _T_3743
      ex_reg_load_use <= id_load_use
      node _T_3744 = and(id_ctrl.jalr, csr.io.status.debug)
      when _T_3744 : 
{
        ex_reg_flush_pipe <= UInt<1>(1)
        ex_ctrl.fence_i <= UInt<1>(1)
        skip
}
      node _T_3747 = or(id_bypass_src_0_0, id_bypass_src_0_1)
      node _T_3748 = or(_T_3747, id_bypass_src_0_2)
      node _T_3749 = or(_T_3748, id_bypass_src_0_3)
      node _T_3754 = mux(id_bypass_src_0_2, UInt<2>(2), UInt<2>(3))
      node _T_3755 = mux(id_bypass_src_0_1, UInt<1>(1), _T_3754)
      node _T_3756 = mux(id_bypass_src_0_0, UInt<1>(0), _T_3755)
      ex_reg_rs_bypass[0] <= _T_3749
      ex_reg_rs_lsb[0] <= _T_3756
      node _T_3758 = eq(_T_3749, UInt<1>(0))
      node _T_3759 = and(id_ctrl.rxs1, _T_3758)
      when _T_3759 : 
{
        node _T_3760 = bits(id_rs_0, 1, 0)
        ex_reg_rs_lsb[0] <= _T_3760
        node _T_3761 = shr(id_rs_0, 2)
        ex_reg_rs_msb[0] <= _T_3761
        skip
}
      node _T_3762 = or(id_bypass_src_1_0, id_bypass_src_1_1)
      node _T_3763 = or(_T_3762, id_bypass_src_1_2)
      node _T_3764 = or(_T_3763, id_bypass_src_1_3)
      node _T_3769 = mux(id_bypass_src_1_2, UInt<2>(2), UInt<2>(3))
      node _T_3770 = mux(id_bypass_src_1_1, UInt<1>(1), _T_3769)
      node _T_3771 = mux(id_bypass_src_1_0, UInt<1>(0), _T_3770)
      ex_reg_rs_bypass[1] <= _T_3764
      ex_reg_rs_lsb[1] <= _T_3771
      node _T_3773 = eq(_T_3764, UInt<1>(0))
      node _T_3774 = and(id_ctrl.rxs2, _T_3773)
      when _T_3774 : 
{
        node _T_3775 = bits(id_rs_1, 1, 0)
        ex_reg_rs_lsb[1] <= _T_3775
        node _T_3776 = shr(id_rs_1, 2)
        ex_reg_rs_msb[1] <= _T_3776
        skip
}
      skip
}
    node _T_3778 = eq(ctrl_killd, UInt<1>(0))
    node _T_3779 = or(_T_3778, csr.io.interrupt)
    node _T_3780 = or(_T_3779, ibuf.io.inst_wky[0].bits_wky.replay)
    when _T_3780 : 
{
      ex_reg_inst <= ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky
      ex_reg_pc <= ibuf.io.pc
      skip
}
    node _T_3781 = or(ex_reg_valid, ex_reg_replay)
    node ex_pc_valid = or(_T_3781, ex_reg_xcpt_interrupt)
    node _T_3783 = eq(io.dmem.resp.valid, UInt<1>(0))
    node wb_dcache_miss = and(wb_ctrl.mem, _T_3783)
    node _T_3785 = eq(io.dmem.req.ready, UInt<1>(0))
    node _T_3786 = and(ex_ctrl.mem, _T_3785)
    node _T_3788 = eq(div_wky.io.req.ready, UInt<1>(0))
    node _T_3789 = and(ex_ctrl.div_wky, _T_3788)
    node replay_ex_structural = or(_T_3786, _T_3789)
    node replay_ex_load_use = and(wb_dcache_miss, ex_reg_load_use)
    node _T_3790 = or(replay_ex_structural, replay_ex_load_use)
    node _T_3791 = and(ex_reg_valid, _T_3790)
    node replay_ex = or(ex_reg_replay, _T_3791)
    node _T_3792 = or(take_pc_mem_wb, replay_ex)
    node _T_3794 = eq(ex_reg_valid, UInt<1>(0))
    node ctrl_killx = or(_T_3792, _T_3794)
    node _T_3796 = eq(ex_ctrl.mem_cmd, UInt<3>(7))
    wire _T_3803 : UInt<3>[4]
    _T_3803 is invalid
    _T_3803[0] <= UInt<1>(0)
    _T_3803[1] <= UInt<3>(4)
    _T_3803[2] <= UInt<1>(1)
    _T_3803[3] <= UInt<3>(5)
    node _T_3810 = eq(_T_3803[0], ex_ctrl.mem_type)
    node _T_3811 = eq(_T_3803[1], ex_ctrl.mem_type)
    node _T_3812 = eq(_T_3803[2], ex_ctrl.mem_type)
    node _T_3813 = eq(_T_3803[3], ex_ctrl.mem_type)
    node _T_3815 = or(UInt<1>(0), _T_3810)
    node _T_3816 = or(_T_3815, _T_3811)
    node _T_3817 = or(_T_3816, _T_3812)
    node _T_3818 = or(_T_3817, _T_3813)
    node ex_slow_bypass = or(_T_3796, _T_3818)
    node ex_xcpt = or(ex_reg_xcpt_interrupt, ex_reg_xcpt)
    node _T_3819 = or(mem_reg_valid, mem_reg_replay)
    node mem_pc_valid = or(_T_3819, mem_reg_xcpt_interrupt)
    node mem_br_taken = bits(mem_reg_wdata, 0, 0)
    node _T_3820 = asSInt(mem_reg_pc)
    node _T_3821 = and(mem_ctrl.branch, mem_br_taken)
    node _T_3824 = eq(UInt<3>(1), UInt<3>(5))
    node _T_3826 = bits(mem_reg_inst, 31, 31)
    node _T_3827 = asSInt(_T_3826)
    node _T_3828 = mux(_T_3824, asSInt(UInt<1>(0)), _T_3827)
    node _T_3830 = eq(UInt<3>(1), UInt<3>(2))
    node _T_3831 = bits(mem_reg_inst, 30, 20)
    node _T_3832 = asSInt(_T_3831)
    node _T_3833 = mux(_T_3830, _T_3832, _T_3828)
    node _T_3835 = neq(UInt<3>(1), UInt<3>(2))
    node _T_3837 = neq(UInt<3>(1), UInt<3>(3))
    node _T_3838 = and(_T_3835, _T_3837)
    node _T_3839 = bits(mem_reg_inst, 19, 12)
    node _T_3840 = asSInt(_T_3839)
    node _T_3841 = mux(_T_3838, _T_3828, _T_3840)
    node _T_3843 = eq(UInt<3>(1), UInt<3>(2))
    node _T_3845 = eq(UInt<3>(1), UInt<3>(5))
    node _T_3846 = or(_T_3843, _T_3845)
    node _T_3849 = eq(UInt<3>(1), UInt<3>(3))
    node _T_3850 = bits(mem_reg_inst, 20, 20)
    node _T_3851 = asSInt(_T_3850)
    node _T_3853 = eq(UInt<3>(1), UInt<3>(1))
    node _T_3854 = bits(mem_reg_inst, 7, 7)
    node _T_3855 = asSInt(_T_3854)
    node _T_3856 = mux(_T_3853, _T_3855, _T_3828)
    node _T_3857 = mux(_T_3849, _T_3851, _T_3856)
    node _T_3858 = mux(_T_3846, asSInt(UInt<1>(0)), _T_3857)
    node _T_3860 = eq(UInt<3>(1), UInt<3>(2))
    node _T_3862 = eq(UInt<3>(1), UInt<3>(5))
    node _T_3863 = or(_T_3860, _T_3862)
    node _T_3865 = bits(mem_reg_inst, 30, 25)
    node _T_3866 = mux(_T_3863, UInt<1>(0), _T_3865)
    node _T_3868 = eq(UInt<3>(1), UInt<3>(2))
    node _T_3871 = eq(UInt<3>(1), UInt<3>(0))
    node _T_3873 = eq(UInt<3>(1), UInt<3>(1))
    node _T_3874 = or(_T_3871, _T_3873)
    node _T_3875 = bits(mem_reg_inst, 11, 8)
    node _T_3877 = eq(UInt<3>(1), UInt<3>(5))
    node _T_3878 = bits(mem_reg_inst, 19, 16)
    node _T_3879 = bits(mem_reg_inst, 24, 21)
    node _T_3880 = mux(_T_3877, _T_3878, _T_3879)
    node _T_3881 = mux(_T_3874, _T_3875, _T_3880)
    node _T_3882 = mux(_T_3868, UInt<1>(0), _T_3881)
    node _T_3884 = eq(UInt<3>(1), UInt<3>(0))
    node _T_3885 = bits(mem_reg_inst, 7, 7)
    node _T_3887 = eq(UInt<3>(1), UInt<3>(4))
    node _T_3888 = bits(mem_reg_inst, 20, 20)
    node _T_3890 = eq(UInt<3>(1), UInt<3>(5))
    node _T_3891 = bits(mem_reg_inst, 15, 15)
    node _T_3893 = mux(_T_3890, _T_3891, UInt<1>(0))
    node _T_3894 = mux(_T_3887, _T_3888, _T_3893)
    node _T_3895 = mux(_T_3884, _T_3885, _T_3894)
    node _T_3896 = cat(_T_3866, _T_3882)
    node _T_3897 = cat(_T_3896, _T_3895)
    node _T_3898 = asUInt(_T_3858)
    node _T_3899 = asUInt(_T_3841)
    node _T_3900 = cat(_T_3899, _T_3898)
    node _T_3901 = asUInt(_T_3833)
    node _T_3902 = asUInt(_T_3828)
    node _T_3903 = cat(_T_3902, _T_3901)
    node _T_3904 = cat(_T_3903, _T_3900)
    node _T_3905 = cat(_T_3904, _T_3897)
    node _T_3906 = asSInt(_T_3905)
    node _T_3908 = and(UInt<1>(1), mem_ctrl.jal)
    node _T_3911 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3913 = bits(mem_reg_inst, 31, 31)
    node _T_3914 = asSInt(_T_3913)
    node _T_3915 = mux(_T_3911, asSInt(UInt<1>(0)), _T_3914)
    node _T_3917 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3918 = bits(mem_reg_inst, 30, 20)
    node _T_3919 = asSInt(_T_3918)
    node _T_3920 = mux(_T_3917, _T_3919, _T_3915)
    node _T_3922 = neq(UInt<3>(3), UInt<3>(2))
    node _T_3924 = neq(UInt<3>(3), UInt<3>(3))
    node _T_3925 = and(_T_3922, _T_3924)
    node _T_3926 = bits(mem_reg_inst, 19, 12)
    node _T_3927 = asSInt(_T_3926)
    node _T_3928 = mux(_T_3925, _T_3915, _T_3927)
    node _T_3930 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3932 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3933 = or(_T_3930, _T_3932)
    node _T_3936 = eq(UInt<3>(3), UInt<3>(3))
    node _T_3937 = bits(mem_reg_inst, 20, 20)
    node _T_3938 = asSInt(_T_3937)
    node _T_3940 = eq(UInt<3>(3), UInt<3>(1))
    node _T_3941 = bits(mem_reg_inst, 7, 7)
    node _T_3942 = asSInt(_T_3941)
    node _T_3943 = mux(_T_3940, _T_3942, _T_3915)
    node _T_3944 = mux(_T_3936, _T_3938, _T_3943)
    node _T_3945 = mux(_T_3933, asSInt(UInt<1>(0)), _T_3944)
    node _T_3947 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3949 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3950 = or(_T_3947, _T_3949)
    node _T_3952 = bits(mem_reg_inst, 30, 25)
    node _T_3953 = mux(_T_3950, UInt<1>(0), _T_3952)
    node _T_3955 = eq(UInt<3>(3), UInt<3>(2))
    node _T_3958 = eq(UInt<3>(3), UInt<3>(0))
    node _T_3960 = eq(UInt<3>(3), UInt<3>(1))
    node _T_3961 = or(_T_3958, _T_3960)
    node _T_3962 = bits(mem_reg_inst, 11, 8)
    node _T_3964 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3965 = bits(mem_reg_inst, 19, 16)
    node _T_3966 = bits(mem_reg_inst, 24, 21)
    node _T_3967 = mux(_T_3964, _T_3965, _T_3966)
    node _T_3968 = mux(_T_3961, _T_3962, _T_3967)
    node _T_3969 = mux(_T_3955, UInt<1>(0), _T_3968)
    node _T_3971 = eq(UInt<3>(3), UInt<3>(0))
    node _T_3972 = bits(mem_reg_inst, 7, 7)
    node _T_3974 = eq(UInt<3>(3), UInt<3>(4))
    node _T_3975 = bits(mem_reg_inst, 20, 20)
    node _T_3977 = eq(UInt<3>(3), UInt<3>(5))
    node _T_3978 = bits(mem_reg_inst, 15, 15)
    node _T_3980 = mux(_T_3977, _T_3978, UInt<1>(0))
    node _T_3981 = mux(_T_3974, _T_3975, _T_3980)
    node _T_3982 = mux(_T_3971, _T_3972, _T_3981)
    node _T_3983 = cat(_T_3953, _T_3969)
    node _T_3984 = cat(_T_3983, _T_3982)
    node _T_3985 = asUInt(_T_3945)
    node _T_3986 = asUInt(_T_3928)
    node _T_3987 = cat(_T_3986, _T_3985)
    node _T_3988 = asUInt(_T_3920)
    node _T_3989 = asUInt(_T_3915)
    node _T_3990 = cat(_T_3989, _T_3988)
    node _T_3991 = cat(_T_3990, _T_3987)
    node _T_3992 = cat(_T_3991, _T_3984)
    node _T_3993 = asSInt(_T_3992)
    node _T_3996 = mux(mem_reg_rvc, asSInt(UInt<3>(2)), asSInt(UInt<4>(4)))
    node _T_3997 = mux(_T_3908, _T_3993, _T_3996)
    node _T_3998 = mux(_T_3821, _T_3906, _T_3997)
    node _T_3999 = add(_T_3820, _T_3998)
    node _T_4000 = tail(_T_3999, 1)
    node mem_br_target = asSInt(_T_4000)
    node _T_4001 = shr(mem_reg_wdata, 38)
    node _T_4002 = bits(mem_reg_wdata, 39, 38)
    node _T_4003 = asSInt(_T_4002)
    node _T_4005 = eq(_T_4001, UInt<1>(0))
    node _T_4007 = eq(_T_4001, UInt<1>(1))
    node _T_4008 = or(_T_4005, _T_4007)
    node _T_4010 = neq(_T_4003, asSInt(UInt<1>(0)))
    node _T_4011 = asSInt(_T_4001)
    node _T_4013 = eq(_T_4011, asSInt(UInt<1>(1)))
    node _T_4014 = asSInt(_T_4001)
    node _T_4016 = eq(_T_4014, asSInt(UInt<2>(2)))
    node _T_4017 = or(_T_4013, _T_4016)
    node _T_4019 = eq(_T_4003, asSInt(UInt<1>(1)))
    node _T_4020 = bits(_T_4003, 0, 0)
    node _T_4021 = mux(_T_4017, _T_4019, _T_4020)
    node _T_4022 = mux(_T_4008, _T_4010, _T_4021)
    node _T_4023 = bits(mem_reg_wdata, 38, 0)
    node _T_4024 = cat(_T_4022, _T_4023)
    node _T_4025 = asSInt(_T_4024)
    node _T_4026 = mux(mem_ctrl.jalr, _T_4025, mem_br_target)
    node _T_4028 = and(_T_4026, asSInt(UInt<2>(2)))
    node _T_4029 = asSInt(_T_4028)
    node mem_npc = asUInt(_T_4029)
    node _T_4030 = neq(mem_npc, ex_reg_pc)
    node _T_4031 = neq(mem_npc, ibuf.io.pc)
    node _T_4033 = mux(ibuf.io.inst_wky[0].valid, _T_4031, UInt<1>(1))
    node mem_misprediction = mux(ex_pc_valid, _T_4030, _T_4033)
    node _T_4034 = bits(csr.io.status.isa, 2, 2)
    node _T_4036 = eq(_T_4034, UInt<1>(0))
    node _T_4037 = bits(mem_npc, 1, 1)
    node mem_npc_misaligned = and(_T_4036, _T_4037)
    node _T_4039 = eq(mem_reg_xcpt, UInt<1>(0))
    node _T_4040 = xor(mem_ctrl.jalr, mem_npc_misaligned)
    node _T_4041 = and(_T_4039, _T_4040)
    node _T_4042 = asSInt(mem_reg_wdata)
    node _T_4043 = mux(_T_4041, mem_br_target, _T_4042)
    node mem_int_wdata = asUInt(_T_4043)
    node _T_4044 = or(mem_ctrl.branch, mem_ctrl.jalr)
    node mem_cfi = or(_T_4044, mem_ctrl.jal)
    node _T_4045 = and(mem_ctrl.branch, mem_br_taken)
    node _T_4046 = or(_T_4045, mem_ctrl.jalr)
    node _T_4048 = and(UInt<1>(1), mem_ctrl.jal)
    node mem_cfi_taken = or(_T_4046, _T_4048)
    node _T_4049 = and(mem_reg_btb_hit, mem_ctrl.branch)
    node _T_4050 = neq(mem_br_taken, mem_reg_btb_resp.taken)
    node mem_direction_misprediction = and(_T_4049, _T_4050)
    node _T_4051 = or(mem_misprediction, mem_reg_flush_pipe)
    node _T_4052 = and(mem_reg_valid, _T_4051)
    take_pc_mem <= _T_4052
    node _T_4054 = eq(ctrl_killx, UInt<1>(0))
    mem_reg_valid <= _T_4054
    node _T_4056 = eq(take_pc_mem_wb, UInt<1>(0))
    node _T_4057 = and(_T_4056, replay_ex)
    mem_reg_replay <= _T_4057
    node _T_4059 = eq(ctrl_killx, UInt<1>(0))
    node _T_4060 = and(_T_4059, ex_xcpt)
    mem_reg_xcpt <= _T_4060
    node _T_4062 = eq(take_pc_mem_wb, UInt<1>(0))
    node _T_4063 = and(_T_4062, ex_reg_xcpt_interrupt)
    mem_reg_xcpt_interrupt <= _T_4063
    when ex_xcpt : 
{
      mem_reg_cause <= ex_cause
      skip
}
    when ex_pc_valid : 
{
      mem_ctrl <= ex_ctrl
      mem_reg_rvc <= ex_reg_rvc
      node _T_4065 = eq(ex_ctrl.mem_cmd, UInt<1>(0))
      node _T_4067 = eq(ex_ctrl.mem_cmd, UInt<3>(6))
      node _T_4068 = or(_T_4065, _T_4067)
      node _T_4070 = eq(ex_ctrl.mem_cmd, UInt<3>(7))
      node _T_4071 = or(_T_4068, _T_4070)
      node _T_4072 = bits(ex_ctrl.mem_cmd, 3, 3)
      node _T_4074 = eq(ex_ctrl.mem_cmd, UInt<3>(4))
      node _T_4075 = or(_T_4072, _T_4074)
      node _T_4076 = or(_T_4071, _T_4075)
      node _T_4077 = and(ex_ctrl.mem, _T_4076)
      mem_reg_load <= _T_4077
      node _T_4079 = eq(ex_ctrl.mem_cmd, UInt<1>(1))
      node _T_4081 = eq(ex_ctrl.mem_cmd, UInt<3>(7))
      node _T_4082 = or(_T_4079, _T_4081)
      node _T_4083 = bits(ex_ctrl.mem_cmd, 3, 3)
      node _T_4085 = eq(ex_ctrl.mem_cmd, UInt<3>(4))
      node _T_4086 = or(_T_4083, _T_4085)
      node _T_4087 = or(_T_4082, _T_4086)
      node _T_4088 = and(ex_ctrl.mem, _T_4087)
      mem_reg_store <= _T_4088
      mem_reg_btb_hit <= ex_reg_btb_hit
      when ex_reg_btb_hit : 
{
        mem_reg_btb_resp <= ex_reg_btb_resp
        skip
}
      mem_reg_flush_pipe <= ex_reg_flush_pipe
      mem_reg_slow_bypass <= ex_slow_bypass
      mem_reg_inst <= ex_reg_inst
      mem_reg_pc <= ex_reg_pc
      mem_reg_wdata <= alu.io.out
      node _T_4089 = or(ex_ctrl.mem, ex_ctrl.rocc)
      node _T_4090 = and(ex_ctrl.rxs2, _T_4089)
      when _T_4090 : 
{
        mem_reg_rs2 <= ex_rs_1
        skip
}
      skip
}
    node _T_4091 = and(mem_reg_load, bpu.io.xcpt_ld)
    node _T_4092 = and(mem_reg_store, bpu.io.xcpt_st)
    node mem_breakpoint = or(_T_4091, _T_4092)
    node _T_4093 = and(mem_reg_load, bpu.io.debug_ld)
    node _T_4094 = and(mem_reg_store, bpu.io.debug_st)
    node mem_debug_breakpoint = or(_T_4093, _T_4094)
    node _T_4126 = and(mem_ctrl.mem, io.dmem.xcpt.ma.st)
    node _T_4128 = and(mem_ctrl.mem, io.dmem.xcpt.ma.ld)
    node _T_4130 = and(mem_ctrl.mem, io.dmem.xcpt.pf.st)
    node _T_4132 = and(mem_ctrl.mem, io.dmem.xcpt.pf.ld)
    node _T_4134 = or(mem_debug_breakpoint, mem_breakpoint)
    node _T_4135 = or(_T_4134, mem_npc_misaligned)
    node _T_4136 = or(_T_4135, _T_4126)
    node _T_4137 = or(_T_4136, _T_4128)
    node _T_4138 = or(_T_4137, _T_4130)
    node mem_new_xcpt = or(_T_4138, _T_4132)
    node _T_4139 = mux(_T_4130, UInt<3>(7), UInt<3>(5))
    node _T_4140 = mux(_T_4128, UInt<3>(4), _T_4139)
    node _T_4141 = mux(_T_4126, UInt<3>(6), _T_4140)
    node _T_4142 = mux(mem_npc_misaligned, UInt<1>(0), _T_4141)
    node _T_4143 = mux(mem_breakpoint, UInt<2>(3), _T_4142)
    node mem_new_cause = mux(mem_debug_breakpoint, UInt<4>(13), _T_4143)
    node _T_4144 = or(mem_reg_xcpt_interrupt, mem_reg_xcpt)
    node _T_4145 = and(mem_reg_valid, mem_new_xcpt)
    node mem_xcpt = or(_T_4144, _T_4145)
    node mem_cause = mux(_T_4144, mem_reg_cause, mem_new_cause)
    node _T_4146 = and(mem_reg_valid, mem_ctrl.wxd)
    node dcache_kill_mem = and(_T_4146, io.dmem.replay_next)
    node _T_4147 = and(mem_reg_valid, mem_ctrl.fp)
    node fpu_kill_mem = and(_T_4147, io.fpu.nack_mem)
    node _T_4148 = or(dcache_kill_mem, mem_reg_replay)
    node replay_mem = or(_T_4148, fpu_kill_mem)
    node _T_4149 = or(dcache_kill_mem, take_pc_wb)
    node _T_4150 = or(_T_4149, mem_reg_xcpt)
    node _T_4152 = eq(mem_reg_valid, UInt<1>(0))
    node killm_common = or(_T_4150, _T_4152)
    node _T_4153 = and(div_wky.io.req.ready, div_wky.io.req.valid)
    reg _T_4154 : UInt<1>, clock 
    _T_4154 <= _T_4153
    node _T_4155 = and(killm_common, _T_4154)
    div_wky.io.kill <= _T_4155
    node _T_4156 = or(killm_common, mem_xcpt)
    node ctrl_killm = or(_T_4156, fpu_kill_mem)
    node _T_4158 = eq(ctrl_killm, UInt<1>(0))
    wb_reg_valid <= _T_4158
    node _T_4160 = eq(take_pc_wb, UInt<1>(0))
    node _T_4161 = and(replay_mem, _T_4160)
    wb_reg_replay <= _T_4161
    node _T_4163 = eq(take_pc_wb, UInt<1>(0))
    node _T_4164 = and(mem_xcpt, _T_4163)
    wb_reg_xcpt <= _T_4164
    when mem_xcpt : 
{
      wb_reg_cause <= mem_cause
      skip
}
    when mem_pc_valid : 
{
      wb_ctrl <= mem_ctrl
      node _T_4166 = eq(mem_reg_xcpt, UInt<1>(0))
      node _T_4167 = and(_T_4166, mem_ctrl.fp)
      node _T_4168 = and(_T_4167, mem_ctrl.wxd)
      node _T_4169 = mux(_T_4168, io.fpu.toint_data, mem_int_wdata)
      wb_reg_wdata <= _T_4169
      when mem_ctrl.rocc : 
{
        wb_reg_rs2 <= mem_reg_rs2
        skip
}
      wb_reg_inst <= mem_reg_inst
      wb_reg_pc <= mem_reg_pc
      skip
}
    node wb_wxd = and(wb_reg_valid, wb_ctrl.wxd)
    node _T_4170 = or(wb_ctrl.div_wky, wb_dcache_miss)
    node wb_set_sboard = or(_T_4170, wb_ctrl.rocc)
    node replay_wb_common = or(io.dmem.s2_nack, wb_reg_replay)
    node _T_4171 = and(wb_reg_valid, wb_ctrl.rocc)
    node _T_4173 = eq(io.rocc.cmd.ready, UInt<1>(0))
    node replay_wb_rocc = and(_T_4171, _T_4173)
    node replay_wb = or(replay_wb_common, replay_wb_rocc)
    node _T_4174 = or(replay_wb, wb_reg_xcpt)
    node _T_4175 = or(_T_4174, csr.io.eret)
    take_pc_wb <= _T_4175
    node _T_4176 = bits(io.dmem.resp.bits_wky.tag, 0, 0)
    node _T_4177 = bits(_T_4176, 0, 0)
    node dmem_resp_xpu = eq(_T_4177, UInt<1>(0))
    node _T_4179 = bits(io.dmem.resp.bits_wky.tag, 0, 0)
    node dmem_resp_fpu = bits(_T_4179, 0, 0)
    node dmem_resp_waddr = bits(io.dmem.resp.bits_wky.tag, 5, 1)
    node dmem_resp_valid = and(io.dmem.resp.valid, io.dmem.resp.bits_wky.has_data)
    node dmem_resp_replay = and(dmem_resp_valid, io.dmem.resp.bits_wky.replay)
    node _T_4181 = eq(wb_wxd, UInt<1>(0))
    div_wky.io.resp.ready <= _T_4181
    wire ll_wdata : UInt<64>
    ll_wdata is invalid
    ll_wdata <= div_wky.io.resp.bits_wky.data
    wire ll_waddr : UInt<5>
    ll_waddr is invalid
    ll_waddr <= div_wky.io.resp.bits_wky.tag
    node _T_4182 = and(div_wky.io.resp.ready, div_wky.io.resp.valid)
    wire ll_wen : UInt<1>
    ll_wen is invalid
    ll_wen <= _T_4182
    node _T_4183 = and(dmem_resp_replay, dmem_resp_xpu)
    when _T_4183 : 
{
      div_wky.io.resp.ready <= UInt<1>(0)
      ll_waddr <= dmem_resp_waddr
      ll_wen <= UInt<1>(1)
      skip
}
    node _T_4187 = eq(replay_wb, UInt<1>(0))
    node _T_4188 = and(wb_reg_valid, _T_4187)
    node _T_4190 = eq(wb_reg_xcpt, UInt<1>(0))
    node wb_valid = and(_T_4188, _T_4190)
    node wb_wen = and(wb_valid, wb_ctrl.wxd)
    node rf_wen = or(wb_wen, ll_wen)
    node rf_waddr = mux(ll_wen, ll_waddr, wb_waddr)
    node _T_4191 = and(dmem_resp_valid, dmem_resp_xpu)
    node _T_4193 = neq(wb_ctrl.csr, UInt<3>(0))
    node _T_4194 = mux(_T_4193, csr.io.rw.rdata, wb_reg_wdata)
    node _T_4195 = mux(ll_wen, ll_wdata, _T_4194)
    node rf_wdata = mux(_T_4191, io.dmem.resp.bits_wky.data, _T_4195)
    when rf_wen : 
{
      node _T_4197 = neq(rf_waddr, UInt<1>(0))
      when _T_4197 : 
{
        node _T_4198 = bits(rf_waddr, 4, 0)
        node _T_4199 = not(_T_4198)
        node _T_4200 = _T_3331[_T_4199]
        _T_4200 <= rf_wdata
        node _T_4201 = eq(rf_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
        when _T_4201 : 
{
          id_rs_0 <= rf_wdata
          skip
}
        node _T_4202 = eq(rf_waddr, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
        when _T_4202 : 
{
          id_rs_1 <= rf_wdata
          skip
}
        skip
}
      skip
}
    node _T_4203 = bits(ibuf.io.inst_wky[0].bits_wky.raw, 31, 20)
    csr.io.decode.csr <= _T_4203
    csr.io.exception <= wb_reg_xcpt
    csr.io.cause <= wb_reg_cause
    csr.io.retire <= wb_valid
    csr.io.interrupts <= io.interrupts
    csr.io.hartid <= io.hartid
    io.fpu.fcsr_rm <= csr.io.fcsr_rm
    csr.io.fcsr_flags <= io.fpu.fcsr_flags
    csr.io.rocc_interrupt <= io.rocc.interrupt
    csr.io.pc <= wb_reg_pc
    node _T_4204 = shr(wb_reg_wdata, 38)
    node _T_4205 = bits(wb_reg_wdata, 39, 38)
    node _T_4206 = asSInt(_T_4205)
    node _T_4208 = eq(_T_4204, UInt<1>(0))
    node _T_4210 = eq(_T_4204, UInt<1>(1))
    node _T_4211 = or(_T_4208, _T_4210)
    node _T_4213 = neq(_T_4206, asSInt(UInt<1>(0)))
    node _T_4214 = asSInt(_T_4204)
    node _T_4216 = eq(_T_4214, asSInt(UInt<1>(1)))
    node _T_4217 = asSInt(_T_4204)
    node _T_4219 = eq(_T_4217, asSInt(UInt<2>(2)))
    node _T_4220 = or(_T_4216, _T_4219)
    node _T_4222 = eq(_T_4206, asSInt(UInt<1>(1)))
    node _T_4223 = bits(_T_4206, 0, 0)
    node _T_4224 = mux(_T_4220, _T_4222, _T_4223)
    node _T_4225 = mux(_T_4211, _T_4213, _T_4224)
    node _T_4226 = bits(wb_reg_wdata, 38, 0)
    node _T_4227 = cat(_T_4225, _T_4226)
    csr.io.badaddr <= _T_4227
    io.ptw.ptbr <= csr.io.ptbr
    io.ptw.invalidate_wky <= csr.io.fatc
    io.ptw.status <= csr.io.status
    node _T_4228 = bits(wb_reg_inst, 31, 20)
    csr.io.rw.addr <= _T_4228
    node _T_4230 = mux(wb_reg_valid, wb_ctrl.csr, UInt<3>(0))
    csr.io.rw.cmd <= _T_4230
    csr.io.rw.wdata <= wb_reg_wdata
    node _T_4232 = neq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, UInt<1>(0))
    node _T_4233 = and(id_ctrl.rxs1, _T_4232)
    node _T_4235 = neq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, UInt<1>(0))
    node _T_4236 = and(id_ctrl.rxs2, _T_4235)
    node _T_4238 = neq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, UInt<1>(0))
    node _T_4239 = and(id_ctrl.wxd, _T_4238)
    regreset _T_4241 : UInt<32>, clock, reset_wky, UInt<32>(0)
    node _T_4242 = shr(_T_4241, 1)
    node _T_4243 = shl(_T_4242, 1)
    node _T_4246 = dshl(UInt<1>(1), ll_waddr)
    node _T_4248 = mux(ll_wen, _T_4246, UInt<1>(0))
    node _T_4249 = not(_T_4248)
    node _T_4250 = and(_T_4243, _T_4249)
    node _T_4251 = or(UInt<1>(0), ll_wen)
    when _T_4251 : 
{
      _T_4241 <= _T_4250
      skip
}
    node _T_4252 = dshr(_T_4243, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node _T_4253 = bits(_T_4252, 0, 0)
    node _T_4254 = and(_T_4233, _T_4253)
    node _T_4255 = dshr(_T_4243, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node _T_4256 = bits(_T_4255, 0, 0)
    node _T_4257 = and(_T_4236, _T_4256)
    node _T_4258 = dshr(_T_4243, ibuf.io.inst_wky[0].bits_wky.inst_wky.rd)
    node _T_4259 = bits(_T_4258, 0, 0)
    node _T_4260 = and(_T_4239, _T_4259)
    node _T_4261 = or(_T_4254, _T_4257)
    node id_sboard_hazard = or(_T_4261, _T_4260)
    node _T_4262 = and(wb_set_sboard, wb_wen)
    node _T_4264 = dshl(UInt<1>(1), wb_waddr)
    node _T_4266 = mux(_T_4262, _T_4264, UInt<1>(0))
    node _T_4267 = or(_T_4250, _T_4266)
    node _T_4268 = or(_T_4251, _T_4262)
    when _T_4268 : 
{
      _T_4241 <= _T_4267
      skip
}
    node _T_4270 = neq(ex_ctrl.csr, UInt<3>(0))
    node _T_4271 = or(_T_4270, ex_ctrl.jalr)
    node _T_4272 = or(_T_4271, ex_ctrl.mem)
    node _T_4273 = or(_T_4272, ex_ctrl.div_wky)
    node _T_4274 = or(_T_4273, ex_ctrl.fp)
    node ex_cannot_bypass = or(_T_4274, ex_ctrl.rocc)
    node _T_4275 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, ex_waddr)
    node _T_4276 = and(_T_4233, _T_4275)
    node _T_4277 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, ex_waddr)
    node _T_4278 = and(_T_4236, _T_4277)
    node _T_4279 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, ex_waddr)
    node _T_4280 = and(_T_4239, _T_4279)
    node _T_4281 = or(_T_4276, _T_4278)
    node _T_4282 = or(_T_4281, _T_4280)
    node data_hazard_ex = and(ex_ctrl.wxd, _T_4282)
    node _T_4283 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, ex_waddr)
    node _T_4284 = and(io.fpu.dec.ren1, _T_4283)
    node _T_4285 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, ex_waddr)
    node _T_4286 = and(io.fpu.dec.ren2, _T_4285)
    node _T_4287 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs3, ex_waddr)
    node _T_4288 = and(io.fpu.dec.ren3, _T_4287)
    node _T_4289 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, ex_waddr)
    node _T_4290 = and(io.fpu.dec.wen, _T_4289)
    node _T_4291 = or(_T_4284, _T_4286)
    node _T_4292 = or(_T_4291, _T_4288)
    node _T_4293 = or(_T_4292, _T_4290)
    node fp_data_hazard_ex = and(ex_ctrl.wfd, _T_4293)
    node _T_4294 = and(data_hazard_ex, ex_cannot_bypass)
    node _T_4295 = or(_T_4294, fp_data_hazard_ex)
    node id_ex_hazard = and(ex_reg_valid, _T_4295)
    node mem_mem_cmd_bh = and(UInt<1>(1), mem_reg_slow_bypass)
    node _T_4298 = neq(mem_ctrl.csr, UInt<3>(0))
    node _T_4299 = and(mem_ctrl.mem, mem_mem_cmd_bh)
    node _T_4300 = or(_T_4298, _T_4299)
    node _T_4301 = or(_T_4300, mem_ctrl.div_wky)
    node _T_4302 = or(_T_4301, mem_ctrl.fp)
    node mem_cannot_bypass = or(_T_4302, mem_ctrl.rocc)
    node _T_4303 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, mem_waddr)
    node _T_4304 = and(_T_4233, _T_4303)
    node _T_4305 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, mem_waddr)
    node _T_4306 = and(_T_4236, _T_4305)
    node _T_4307 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, mem_waddr)
    node _T_4308 = and(_T_4239, _T_4307)
    node _T_4309 = or(_T_4304, _T_4306)
    node _T_4310 = or(_T_4309, _T_4308)
    node data_hazard_mem = and(mem_ctrl.wxd, _T_4310)
    node _T_4311 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, mem_waddr)
    node _T_4312 = and(io.fpu.dec.ren1, _T_4311)
    node _T_4313 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, mem_waddr)
    node _T_4314 = and(io.fpu.dec.ren2, _T_4313)
    node _T_4315 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs3, mem_waddr)
    node _T_4316 = and(io.fpu.dec.ren3, _T_4315)
    node _T_4317 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, mem_waddr)
    node _T_4318 = and(io.fpu.dec.wen, _T_4317)
    node _T_4319 = or(_T_4312, _T_4314)
    node _T_4320 = or(_T_4319, _T_4316)
    node _T_4321 = or(_T_4320, _T_4318)
    node fp_data_hazard_mem = and(mem_ctrl.wfd, _T_4321)
    node _T_4322 = and(data_hazard_mem, mem_cannot_bypass)
    node _T_4323 = or(_T_4322, fp_data_hazard_mem)
    node id_mem_hazard = and(mem_reg_valid, _T_4323)
    node _T_4324 = and(mem_reg_valid, data_hazard_mem)
    node _T_4325 = and(_T_4324, mem_ctrl.mem)
    id_load_use <= _T_4325
    node _T_4326 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, wb_waddr)
    node _T_4327 = and(_T_4233, _T_4326)
    node _T_4328 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, wb_waddr)
    node _T_4329 = and(_T_4236, _T_4328)
    node _T_4330 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, wb_waddr)
    node _T_4331 = and(_T_4239, _T_4330)
    node _T_4332 = or(_T_4327, _T_4329)
    node _T_4333 = or(_T_4332, _T_4331)
    node data_hazard_wb = and(wb_ctrl.wxd, _T_4333)
    node _T_4334 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1, wb_waddr)
    node _T_4335 = and(io.fpu.dec.ren1, _T_4334)
    node _T_4336 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2, wb_waddr)
    node _T_4337 = and(io.fpu.dec.ren2, _T_4336)
    node _T_4338 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rs3, wb_waddr)
    node _T_4339 = and(io.fpu.dec.ren3, _T_4338)
    node _T_4340 = eq(ibuf.io.inst_wky[0].bits_wky.inst_wky.rd, wb_waddr)
    node _T_4341 = and(io.fpu.dec.wen, _T_4340)
    node _T_4342 = or(_T_4335, _T_4337)
    node _T_4343 = or(_T_4342, _T_4339)
    node _T_4344 = or(_T_4343, _T_4341)
    node fp_data_hazard_wb = and(wb_ctrl.wfd, _T_4344)
    node _T_4345 = and(data_hazard_wb, wb_set_sboard)
    node _T_4346 = or(_T_4345, fp_data_hazard_wb)
    node id_wb_hazard = and(wb_reg_valid, _T_4346)
    regreset _T_4348 : UInt<32>, clock, reset_wky, UInt<32>(0)
    node _T_4350 = and(wb_dcache_miss, wb_ctrl.wfd)
    node _T_4351 = or(_T_4350, io.fpu.sboard_set)
    node _T_4352 = and(_T_4351, wb_valid)
    node _T_4354 = dshl(UInt<1>(1), wb_waddr)
    node _T_4356 = mux(_T_4352, _T_4354, UInt<1>(0))
    node _T_4357 = or(_T_4348, _T_4356)
    node _T_4358 = or(UInt<1>(0), _T_4352)
    when _T_4358 : 
{
      _T_4348 <= _T_4357
      skip
}
    node _T_4359 = and(dmem_resp_replay, dmem_resp_fpu)
    node _T_4361 = dshl(UInt<1>(1), dmem_resp_waddr)
    node _T_4363 = mux(_T_4359, _T_4361, UInt<1>(0))
    node _T_4364 = not(_T_4363)
    node _T_4365 = and(_T_4357, _T_4364)
    node _T_4366 = or(_T_4358, _T_4359)
    when _T_4366 : 
{
      _T_4348 <= _T_4365
      skip
}
    node _T_4368 = dshl(UInt<1>(1), io.fpu.sboard_clra)
    node _T_4370 = mux(io.fpu.sboard_clr, _T_4368, UInt<1>(0))
    node _T_4371 = not(_T_4370)
    node _T_4372 = and(_T_4365, _T_4371)
    node _T_4373 = or(_T_4366, io.fpu.sboard_clr)
    when _T_4373 : 
{
      _T_4348 <= _T_4372
      skip
}
    node _T_4375 = eq(io.fpu.fcsr_rdy, UInt<1>(0))
    node _T_4376 = and(id_csr_en, _T_4375)
    node _T_4377 = dshr(_T_4348, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs1)
    node _T_4378 = bits(_T_4377, 0, 0)
    node _T_4379 = and(io.fpu.dec.ren1, _T_4378)
    node _T_4380 = dshr(_T_4348, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs2)
    node _T_4381 = bits(_T_4380, 0, 0)
    node _T_4382 = and(io.fpu.dec.ren2, _T_4381)
    node _T_4383 = dshr(_T_4348, ibuf.io.inst_wky[0].bits_wky.inst_wky.rs3)
    node _T_4384 = bits(_T_4383, 0, 0)
    node _T_4385 = and(io.fpu.dec.ren3, _T_4384)
    node _T_4386 = dshr(_T_4348, ibuf.io.inst_wky[0].bits_wky.inst_wky.rd)
    node _T_4387 = bits(_T_4386, 0, 0)
    node _T_4388 = and(io.fpu.dec.wen, _T_4387)
    node _T_4389 = or(_T_4379, _T_4382)
    node _T_4390 = or(_T_4389, _T_4385)
    node _T_4391 = or(_T_4390, _T_4388)
    node id_stall_fpu = or(_T_4376, _T_4391)
    reg dcache_blocked : UInt<1>, clock 
    node _T_4394 = eq(io.dmem.req.ready, UInt<1>(0))
    node _T_4395 = or(io.dmem.req.valid, dcache_blocked)
    node _T_4396 = and(_T_4394, _T_4395)
    dcache_blocked <= _T_4396
    reg rocc_blocked : UInt<1>, clock 
    node _T_4399 = eq(wb_reg_xcpt, UInt<1>(0))
    node _T_4401 = eq(io.rocc.cmd.ready, UInt<1>(0))
    node _T_4402 = and(_T_4399, _T_4401)
    node _T_4403 = or(io.rocc.cmd.valid, rocc_blocked)
    node _T_4404 = and(_T_4402, _T_4403)
    rocc_blocked <= _T_4404
    node _T_4405 = or(id_ex_hazard, id_mem_hazard)
    node _T_4406 = or(_T_4405, id_wb_hazard)
    node _T_4407 = or(_T_4406, id_sboard_hazard)
    node _T_4408 = and(id_ctrl.fp, id_stall_fpu)
    node _T_4409 = or(_T_4407, _T_4408)
    node _T_4410 = and(id_ctrl.mem, dcache_blocked)
    node _T_4411 = or(_T_4409, _T_4410)
    node _T_4412 = and(id_ctrl.rocc, rocc_blocked)
    node _T_4413 = or(_T_4411, _T_4412)
    node _T_4415 = eq(wb_wxd, UInt<1>(0))
    node _T_4416 = and(div_wky.io.resp.valid, _T_4415)
    node _T_4417 = or(div_wky.io.req.ready, _T_4416)
    node _T_4419 = eq(_T_4417, UInt<1>(0))
    node _T_4420 = or(_T_4419, div_wky.io.req.valid)
    node _T_4421 = and(id_ctrl.div_wky, _T_4420)
    node _T_4422 = or(_T_4413, _T_4421)
    node _T_4423 = or(_T_4422, id_do_fence)
    node ctrl_stalld = or(_T_4423, csr.io.csr_stall)
    node _T_4425 = eq(ibuf.io.inst_wky[0].valid, UInt<1>(0))
    node _T_4426 = or(_T_4425, ibuf.io.inst_wky[0].bits_wky.replay)
    node _T_4427 = or(_T_4426, take_pc_mem_wb)
    node _T_4428 = or(_T_4427, ctrl_stalld)
    node _T_4429 = or(_T_4428, csr.io.interrupt)
    ctrl_killd <= _T_4429
    io.imem.req.valid <= take_pc
    node _T_4431 = eq(take_pc_wb, UInt<1>(0))
    io.imem.req.bits_wky.speculative <= _T_4431
    node _T_4432 = or(wb_reg_xcpt, csr.io.eret)
    node _T_4434 = or(take_pc_mem, UInt<1>(1))
    node _T_4435 = mux(_T_4434, mem_npc, id_npc)
    node _T_4436 = mux(replay_wb, wb_reg_pc, _T_4435)
    node _T_4437 = mux(_T_4432, csr.io.evec, _T_4436)
    io.imem.req.bits_wky.pc <= _T_4437
    node _T_4438 = and(wb_reg_valid, wb_ctrl.fence_i)
    node _T_4440 = eq(io.dmem.s2_nack, UInt<1>(0))
    node _T_4441 = and(_T_4438, _T_4440)
    io.imem.flush_icache <= _T_4441
    io.imem.flush_tlb <= csr.io.fatc
    node _T_4443 = eq(ctrl_stalld, UInt<1>(0))
    node _T_4444 = or(_T_4443, csr.io.interrupt)
    ibuf.io.inst_wky[0].ready <= _T_4444
    node _T_4445 = and(mem_reg_replay, mem_reg_btb_hit)
    node _T_4447 = eq(take_pc_wb, UInt<1>(0))
    node _T_4448 = and(mem_reg_valid, _T_4447)
    node _T_4450 = eq(mem_cfi, UInt<1>(0))
    node _T_4451 = or(mem_cfi_taken, _T_4450)
    node _T_4452 = and(_T_4451, mem_misprediction)
    node _T_4454 = and(UInt<1>(0), mem_ctrl.jal)
    node _T_4456 = eq(mem_reg_btb_hit, UInt<1>(0))
    node _T_4457 = and(_T_4454, _T_4456)
    node _T_4458 = or(_T_4452, _T_4457)
    node _T_4459 = and(_T_4448, _T_4458)
    node _T_4460 = or(_T_4445, _T_4459)
    io.imem.btb_update.valid <= _T_4460
    node _T_4462 = eq(mem_reg_replay, UInt<1>(0))
    node _T_4463 = and(_T_4462, mem_cfi)
    io.imem.btb_update.bits_wky.isValid <= _T_4463
    node _T_4464 = or(mem_ctrl.jal, mem_ctrl.jalr)
    io.imem.btb_update.bits_wky.isJump <= _T_4464
    node _T_4465 = bits(mem_reg_inst, 19, 15)
    node _T_4468 = and(_T_4465, UInt<5>(27))
    node _T_4469 = eq(UInt<1>(1), _T_4468)
    node _T_4470 = and(mem_ctrl.jalr, _T_4469)
    io.imem.btb_update.bits_wky.isReturn <= _T_4470
    io.imem.btb_update.bits_wky.target <= io.imem.req.bits_wky.pc
    node _T_4473 = mux(mem_reg_rvc, UInt<1>(0), UInt<2>(2))
    node _T_4474 = add(mem_reg_pc, _T_4473)
    node _T_4475 = tail(_T_4474, 1)
    io.imem.btb_update.bits_wky.br_pc <= _T_4475
    node _T_4476 = not(io.imem.btb_update.bits_wky.br_pc)
    node _T_4478 = or(_T_4476, UInt<2>(3))
    node _T_4479 = not(_T_4478)
    io.imem.btb_update.bits_wky.pc <= _T_4479
    io.imem.btb_update.bits_wky.prediction.valid <= mem_reg_btb_hit
    io.imem.btb_update.bits_wky.prediction.bits_wky <= mem_reg_btb_resp
    node _T_4481 = eq(take_pc_wb, UInt<1>(0))
    node _T_4482 = and(mem_reg_valid, _T_4481)
    node _T_4483 = and(_T_4482, mem_ctrl.branch)
    io.imem.bht_update.valid <= _T_4483
    io.imem.bht_update.bits_wky.pc <= io.imem.btb_update.bits_wky.pc
    io.imem.bht_update.bits_wky.taken <= mem_br_taken
    io.imem.bht_update.bits_wky.mispredict <= mem_misprediction
    io.imem.bht_update.bits_wky.prediction <= io.imem.btb_update.bits_wky.prediction
    node _T_4485 = eq(take_pc_wb, UInt<1>(0))
    node _T_4486 = and(mem_reg_valid, _T_4485)
    io.imem.ras_update.valid <= _T_4486
    io.imem.ras_update.bits_wky.returnAddr <= mem_int_wdata
    node _T_4487 = bits(mem_waddr, 0, 0)
    node _T_4488 = and(io.imem.btb_update.bits_wky.isJump, _T_4487)
    io.imem.ras_update.bits_wky.isCall <= _T_4488
    io.imem.ras_update.bits_wky.isReturn <= io.imem.btb_update.bits_wky.isReturn
    io.imem.ras_update.bits_wky.prediction <= io.imem.btb_update.bits_wky.prediction
    node _T_4490 = eq(ctrl_killd, UInt<1>(0))
    node _T_4491 = and(_T_4490, id_ctrl.fp)
    io.fpu.valid <= _T_4491
    io.fpu.killx <= ctrl_killx
    io.fpu.killm <= killm_common
    io.fpu.inst_wky <= ibuf.io.inst_wky[0].bits_wky.inst_wky.bits_wky
    io.fpu.fromint_data <= ex_rs_0
    node _T_4492 = and(dmem_resp_valid, dmem_resp_fpu)
    io.fpu.dmem_resp_val <= _T_4492
    io.fpu.dmem_resp_data <= io.dmem.resp.bits_wky.data_word_bypass
    io.fpu.dmem_resp_type <= io.dmem.resp.bits_wky.typ
    io.fpu.dmem_resp_tag <= dmem_resp_waddr
    node _T_4493 = and(ex_reg_valid, ex_ctrl.mem)
    io.dmem.req.valid <= _T_4493
    node ex_dcache_tag = cat(ex_waddr, ex_ctrl.fp)
    io.dmem.req.bits_wky.tag <= ex_dcache_tag
    io.dmem.req.bits_wky.cmd <= ex_ctrl.mem_cmd
    io.dmem.req.bits_wky.typ <= ex_ctrl.mem_type
    io.dmem.req.bits_wky.phys <= UInt<1>(0)
    node _T_4495 = shr(ex_rs_0, 38)
    node _T_4496 = bits(alu.io.adder_out, 39, 38)
    node _T_4497 = asSInt(_T_4496)
    node _T_4499 = eq(_T_4495, UInt<1>(0))
    node _T_4501 = eq(_T_4495, UInt<1>(1))
    node _T_4502 = or(_T_4499, _T_4501)
    node _T_4504 = neq(_T_4497, asSInt(UInt<1>(0)))
    node _T_4505 = asSInt(_T_4495)
    node _T_4507 = eq(_T_4505, asSInt(UInt<1>(1)))
    node _T_4508 = asSInt(_T_4495)
    node _T_4510 = eq(_T_4508, asSInt(UInt<2>(2)))
    node _T_4511 = or(_T_4507, _T_4510)
    node _T_4513 = eq(_T_4497, asSInt(UInt<1>(1)))
    node _T_4514 = bits(_T_4497, 0, 0)
    node _T_4515 = mux(_T_4511, _T_4513, _T_4514)
    node _T_4516 = mux(_T_4502, _T_4504, _T_4515)
    node _T_4517 = bits(alu.io.adder_out, 38, 0)
    node _T_4518 = cat(_T_4516, _T_4517)
    io.dmem.req.bits_wky.addr <= _T_4518
    io.dmem.invalidate_lr <= wb_reg_xcpt
    node _T_4519 = mux(mem_ctrl.fp, io.fpu.store_data, mem_reg_rs2)
    io.dmem.s1_data <= _T_4519
    node _T_4520 = or(killm_common, mem_breakpoint)
    io.dmem.s1_kill <= _T_4520
    node _T_4521 = and(mem_ctrl.mem, mem_xcpt)
    node _T_4523 = eq(io.dmem.s1_kill, UInt<1>(0))
    node _T_4524 = and(_T_4521, _T_4523)
    when _T_4524 : 
{
      node _T_4525 = cat(io.dmem.xcpt.pf.ld, io.dmem.xcpt.pf.st)
      node _T_4526 = cat(io.dmem.xcpt.ma.ld, io.dmem.xcpt.ma.st)
      node _T_4527 = cat(_T_4526, _T_4525)
      node _T_4529 = neq(_T_4527, UInt<1>(0))
      node _T_4530 = or(_T_4529, reset_wky)
      node _T_4532 = eq(_T_4530, UInt<1>(0))
      when _T_4532 : 
{
        skip
}
      skip
}
    node _T_4533 = and(wb_reg_valid, wb_ctrl.rocc)
    node _T_4535 = eq(replay_wb_common, UInt<1>(0))
    node _T_4536 = and(_T_4533, _T_4535)
    io.rocc.cmd.valid <= _T_4536
    node _T_4538 = neq(csr.io.status.xs, UInt<1>(0))
    node _T_4539 = and(wb_reg_xcpt, _T_4538)
    io.rocc.exception <= _T_4539
    io.rocc.cmd.bits_wky.status <= csr.io.status
    wire _T_4558 : {funct : UInt<7>, rs2 : UInt<5>, rs1 : UInt<5>, xd : UInt<1>, xs1 : UInt<1>, xs2 : UInt<1>, rd : UInt<5>, opcode : UInt<7>}
    _T_4558 is invalid
    wire _T_4568 : UInt<32>
    _T_4568 is invalid
    _T_4568 <= wb_reg_inst
    node _T_4569 = bits(_T_4568, 6, 0)
    _T_4558.opcode <= _T_4569
    node _T_4570 = bits(_T_4568, 11, 7)
    _T_4558.rd <= _T_4570
    node _T_4571 = bits(_T_4568, 12, 12)
    _T_4558.xs2 <= _T_4571
    node _T_4572 = bits(_T_4568, 13, 13)
    _T_4558.xs1 <= _T_4572
    node _T_4573 = bits(_T_4568, 14, 14)
    _T_4558.xd <= _T_4573
    node _T_4574 = bits(_T_4568, 19, 15)
    _T_4558.rs1 <= _T_4574
    node _T_4575 = bits(_T_4568, 24, 20)
    _T_4558.rs2 <= _T_4575
    node _T_4576 = bits(_T_4568, 31, 25)
    _T_4558.funct <= _T_4576
    io.rocc.cmd.bits_wky.inst_wky <= _T_4558
    io.rocc.cmd.bits_wky.rs1 <= wb_reg_wdata
    io.rocc.cmd.bits_wky.rs2 <= wb_reg_rs2
    node _T_4577 = bits(csr.io.time, 31, 0)
    node _T_4579 = mux(rf_wen, rf_waddr, UInt<1>(0))
    node _T_4580 = bits(wb_reg_inst, 19, 15)
    reg _T_4581 : UInt<64>, clock 
    _T_4581 <= ex_rs_0
    reg _T_4582 : UInt<64>, clock 
    _T_4582 <= _T_4581
    node _T_4583 = bits(wb_reg_inst, 24, 20)
    reg _T_4584 : UInt<64>, clock 
    _T_4584 <= ex_rs_1
    reg _T_4585 : UInt<64>, clock 
    _T_4585 <= _T_4584
    node _T_4587 = eq(reset_wky, UInt<1>(0))
    when _T_4587 : 
{
      skip
}
  module IBuf : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip imem : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {btb : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}, pc : UInt<40>, data : UInt<32>, mask : UInt<2>, xcpt_if : UInt<1>, replay : UInt<1>}},  flip kill : UInt<1>, pc : UInt<40>, btb_resp : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}, inst_wky : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {pf0 : UInt<1>, pf1 : UInt<1>, replay : UInt<1>, btb_hit : UInt<1>, rvc : UInt<1>, inst_wky : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}, raw : UInt<32>}}[1]}
    io is invalid
    io is invalid
    regreset nBufValid : UInt<1>, clock, reset_wky, UInt<1>(0)
    reg buf : {btb : {valid : UInt<1>, bits_wky : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}}, pc : UInt<40>, data : UInt<32>, mask : UInt<2>, xcpt_if : UInt<1>, replay : UInt<1>}, clock 
    reg ibufBTBHit : UInt<1>, clock 
    reg ibufBTBResp : {taken : UInt<1>, mask : UInt<2>, bridx : UInt<1>, target : UInt<39>, entry : UInt<6>, bht : {history : UInt<7>, value : UInt<2>}}, clock 
    node pcWordBits = bits(io.imem.bits_wky.pc, 1, 1)
    wire nReady : UInt<2>
    nReady is invalid
    nReady <= UInt<2>(0)
    node _T_375 = and(io.imem.bits_wky.btb.valid, io.imem.bits_wky.btb.bits_wky.taken)
    node _T_377 = add(io.imem.bits_wky.btb.bits_wky.bridx, UInt<1>(1))
    node _T_379 = mux(_T_375, _T_377, UInt<2>(2))
    node _T_380 = sub(_T_379, pcWordBits)
    node _T_381 = asUInt(_T_380)
    node nIC = tail(_T_381, 1)
    node _T_382 = sub(nReady, nBufValid)
    node _T_383 = asUInt(_T_382)
    node nICReady = tail(_T_383, 1)
    node _T_385 = mux(io.imem.valid, nIC, UInt<1>(0))
    node _T_386 = add(_T_385, nBufValid)
    node nValid = tail(_T_386, 1)
    node _T_387 = geq(nReady, nBufValid)
    node _T_388 = geq(nICReady, nIC)
    node _T_390 = sub(nIC, nICReady)
    node _T_391 = asUInt(_T_390)
    node _T_392 = tail(_T_391, 1)
    node _T_393 = geq(UInt<1>(1), _T_392)
    node _T_394 = or(_T_388, _T_393)
    node _T_395 = and(_T_387, _T_394)
    io.imem.ready <= _T_395
    node _T_396 = geq(nReady, nBufValid)
    node _T_398 = sub(nBufValid, nReady)
    node _T_399 = asUInt(_T_398)
    node _T_400 = tail(_T_399, 1)
    node _T_401 = mux(_T_396, UInt<1>(0), _T_400)
    nBufValid <= _T_401
    node _T_402 = geq(nReady, nBufValid)
    node _T_403 = and(io.imem.valid, _T_402)
    node _T_404 = lt(nICReady, nIC)
    node _T_405 = and(_T_403, _T_404)
    node _T_407 = sub(nIC, nICReady)
    node _T_408 = asUInt(_T_407)
    node _T_409 = tail(_T_408, 1)
    node _T_410 = geq(UInt<1>(1), _T_409)
    node _T_411 = and(_T_405, _T_410)
    when _T_411 : 
{
      node _T_412 = add(pcWordBits, nICReady)
      node _T_413 = tail(_T_412, 1)
      node _T_414 = sub(nIC, nICReady)
      node _T_415 = asUInt(_T_414)
      node _T_416 = tail(_T_415, 1)
      nBufValid <= _T_416
      buf <= io.imem.bits_wky
      node _T_417 = shr(io.imem.bits_wky.data, 16)
      node _T_418 = cat(_T_417, _T_417)
      node _T_419 = cat(_T_418, io.imem.bits_wky.data)
      node _T_420 = shl(_T_413, 4)
      node _T_421 = dshr(_T_419, _T_420)
      node _T_422 = bits(_T_421, 15, 0)
      buf.data <= _T_422
      node _T_423 = not(UInt<40>(3))
      node _T_424 = and(io.imem.bits_wky.pc, _T_423)
      node _T_425 = shl(nICReady, 1)
      node _T_426 = add(io.imem.bits_wky.pc, _T_425)
      node _T_427 = tail(_T_426, 1)
      node _T_428 = and(_T_427, UInt<40>(3))
      node _T_429 = or(_T_424, _T_428)
      buf.pc <= _T_429
      ibufBTBHit <= io.imem.bits_wky.btb.valid
      when io.imem.bits_wky.btb.valid : 
{
        ibufBTBResp <= io.imem.bits_wky.btb.bits_wky
        node _T_430 = add(io.imem.bits_wky.btb.bits_wky.bridx, nICReady)
        node _T_431 = tail(_T_430, 1)
        ibufBTBResp.bridx <= _T_431
        skip
}
      skip
}
    when io.kill : 
{
      nBufValid <= UInt<1>(0)
      skip
}
    node _T_434 = add(UInt<2>(2), nBufValid)
    node _T_435 = tail(_T_434, 1)
    node _T_436 = sub(_T_435, pcWordBits)
    node _T_437 = asUInt(_T_436)
    node _T_438 = tail(_T_437, 1)
    node icShiftAmt = bits(_T_438, 1, 0)
    node _T_439 = bits(io.imem.bits_wky.data, 15, 0)
    node _T_440 = cat(_T_439, _T_439)
    node _T_441 = cat(io.imem.bits_wky.data, _T_440)
    node _T_442 = shr(_T_441, 48)
    node _T_443 = cat(_T_442, _T_442)
    node _T_444 = cat(_T_443, _T_443)
    node _T_445 = cat(_T_444, _T_441)
    node _T_446 = shl(icShiftAmt, 4)
    node _T_447 = dshl(_T_445, _T_446)
    node icData = bits(_T_447, 95, 64)
    node _T_449 = not(UInt<32>(0))
    node _T_450 = shl(nBufValid, 4)
    node _T_451 = dshl(_T_449, _T_450)
    node icMask = bits(_T_451, 31, 0)
    node _T_452 = and(icData, icMask)
    node _T_453 = not(icMask)
    node _T_454 = and(buf.data, _T_453)
    node inst_wky = or(_T_452, _T_454)
    node _T_456 = dshl(UInt<1>(1), nValid)
    node _T_458 = sub(_T_456, UInt<1>(1))
    node _T_459 = asUInt(_T_458)
    node _T_460 = tail(_T_459, 1)
    node valid = bits(_T_460, 1, 0)
    node _T_462 = dshl(UInt<1>(1), nBufValid)
    node _T_464 = sub(_T_462, UInt<1>(1))
    node _T_465 = asUInt(_T_464)
    node bufMask = tail(_T_465, 1)
    node _T_467 = mux(buf.xcpt_if, bufMask, UInt<1>(0))
    node _T_468 = not(bufMask)
    node _T_470 = mux(io.imem.bits_wky.xcpt_if, _T_468, UInt<1>(0))
    node _T_471 = or(_T_467, _T_470)
    node xcpt_if = and(valid, _T_471)
    node _T_473 = mux(buf.replay, bufMask, UInt<1>(0))
    node _T_474 = not(bufMask)
    node _T_476 = mux(io.imem.bits_wky.replay, _T_474, UInt<1>(0))
    node _T_477 = or(_T_473, _T_476)
    node ic_replay = and(valid, _T_477)
    node _T_479 = dshl(UInt<1>(1), ibufBTBResp.bridx)
    node ibufBTBHitMask = mux(ibufBTBHit, _T_479, UInt<1>(0))
    node _T_482 = eq(io.imem.bits_wky.btb.valid, UInt<1>(0))
    node _T_483 = geq(io.imem.bits_wky.btb.bits_wky.bridx, pcWordBits)
    node _T_484 = or(_T_482, _T_483)
    node _T_485 = or(_T_484, reset_wky)
    node _T_487 = eq(_T_485, UInt<1>(0))
    when _T_487 : 
{
      skip
}
    node _T_488 = add(io.imem.bits_wky.btb.bits_wky.bridx, nBufValid)
    node _T_489 = sub(_T_488, pcWordBits)
    node _T_490 = asUInt(_T_489)
    node _T_491 = tail(_T_490, 1)
    node _T_493 = dshl(UInt<1>(1), _T_491)
    node icBTBHitMask = mux(io.imem.bits_wky.btb.valid, _T_493, UInt<1>(0))
    node _T_495 = and(ibufBTBHitMask, bufMask)
    node _T_496 = not(bufMask)
    node _T_497 = and(icBTBHitMask, _T_496)
    node btbHitMask = or(_T_495, _T_497)
    node _T_498 = and(ibufBTBHitMask, bufMask)
    node _T_500 = neq(_T_498, UInt<1>(0))
    node _T_501 = mux(_T_500, ibufBTBResp, io.imem.bits_wky.btb.bits_wky)
    io.btb_resp <= _T_501
    node _T_511 = gt(nBufValid, UInt<1>(0))
    node _T_512 = mux(_T_511, buf.pc, io.imem.bits_wky.pc)
    io.pc <= _T_512
    inst RVCExpander aof RVCExpander
    RVCExpander.io is invalid
    RVCExpander.clock <= clock
    RVCExpander.reset_wky <= reset_wky
    RVCExpander.io.in <= inst_wky
    io.inst_wky[0].bits_wky.inst_wky <= RVCExpander.io.out
    io.inst_wky[0].bits_wky.raw <= inst_wky
    node _T_514 = dshr(ic_replay, UInt<1>(0))
    node _T_515 = bits(_T_514, 0, 0)
    node _T_517 = eq(RVCExpander.io.rvc, UInt<1>(0))
    node _T_518 = dshr(btbHitMask, UInt<1>(0))
    node _T_519 = bits(_T_518, 0, 0)
    node _T_521 = add(UInt<1>(0), UInt<1>(1))
    node _T_522 = tail(_T_521, 1)
    node _T_523 = dshr(ic_replay, _T_522)
    node _T_524 = bits(_T_523, 0, 0)
    node _T_525 = or(_T_519, _T_524)
    node _T_526 = and(_T_517, _T_525)
    node _T_527 = or(_T_515, _T_526)
    node _T_528 = dshr(valid, UInt<1>(0))
    node _T_529 = bits(_T_528, 0, 0)
    node _T_531 = add(UInt<1>(0), UInt<1>(1))
    node _T_532 = tail(_T_531, 1)
    node _T_533 = dshr(valid, _T_532)
    node _T_534 = bits(_T_533, 0, 0)
    node _T_535 = or(RVCExpander.io.rvc, _T_534)
    node _T_537 = add(UInt<1>(0), UInt<1>(1))
    node _T_538 = tail(_T_537, 1)
    node _T_539 = dshr(xcpt_if, _T_538)
    node _T_540 = bits(_T_539, 0, 0)
    node _T_541 = or(_T_535, _T_540)
    node _T_542 = or(_T_541, _T_527)
    node _T_543 = and(_T_529, _T_542)
    io.inst_wky[0].valid <= _T_543
    node _T_544 = dshr(xcpt_if, UInt<1>(0))
    node _T_545 = bits(_T_544, 0, 0)
    io.inst_wky[0].bits_wky.pf0 <= _T_545
    node _T_547 = eq(RVCExpander.io.rvc, UInt<1>(0))
    node _T_549 = add(UInt<1>(0), UInt<1>(1))
    node _T_550 = tail(_T_549, 1)
    node _T_551 = dshr(xcpt_if, _T_550)
    node _T_552 = bits(_T_551, 0, 0)
    node _T_553 = and(_T_547, _T_552)
    io.inst_wky[0].bits_wky.pf1 <= _T_553
    io.inst_wky[0].bits_wky.replay <= _T_527
    node _T_554 = dshr(btbHitMask, UInt<1>(0))
    node _T_555 = bits(_T_554, 0, 0)
    node _T_557 = eq(RVCExpander.io.rvc, UInt<1>(0))
    node _T_559 = add(UInt<1>(0), UInt<1>(1))
    node _T_560 = tail(_T_559, 1)
    node _T_561 = dshr(btbHitMask, _T_560)
    node _T_562 = bits(_T_561, 0, 0)
    node _T_563 = and(_T_557, _T_562)
    node _T_564 = or(_T_555, _T_563)
    io.inst_wky[0].bits_wky.btb_hit <= _T_564
    io.inst_wky[0].bits_wky.rvc <= RVCExpander.io.rvc
    node _T_565 = and(io.inst_wky[0].ready, io.inst_wky[0].valid)
    when _T_565 : 
{
      node _T_567 = add(UInt<1>(0), UInt<1>(1))
      node _T_568 = tail(_T_567, 1)
      node _T_570 = add(UInt<1>(0), UInt<2>(2))
      node _T_571 = tail(_T_570, 1)
      node _T_572 = mux(RVCExpander.io.rvc, _T_568, _T_571)
      nReady <= _T_572
      skip
}
    node _T_574 = add(UInt<1>(0), UInt<1>(1))
    node _T_575 = tail(_T_574, 1)
    node _T_577 = add(UInt<1>(0), UInt<2>(2))
    node _T_578 = tail(_T_577, 1)
    node _T_579 = mux(RVCExpander.io.rvc, _T_575, _T_578)
    node _T_580 = shr(inst_wky, 16)
    node _T_581 = shr(inst_wky, 32)
    node _T_582 = mux(RVCExpander.io.rvc, _T_580, _T_581)
  module CSRFile : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip interrupts : {debug : UInt<1>, mtip : UInt<1>, msip : UInt<1>, meip : UInt<1>, seip : UInt<1>},  flip hartid : UInt<64>, rw : { flip addr : UInt<12>,  flip cmd : UInt<3>, rdata : UInt<64>,  flip wdata : UInt<64>}, decode : { flip csr : UInt<12>, fp_illegal : UInt<1>, rocc_illegal : UInt<1>, read_illegal : UInt<1>, write_illegal : UInt<1>, write_flush : UInt<1>, system_illegal : UInt<1>}, csr_stall : UInt<1>, eret : UInt<1>, singleStep : UInt<1>, status : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}, ptbr : {mode : UInt<4>, asid : UInt<16>, ppn : UInt<44>}, evec : UInt<40>,  flip exception : UInt<1>,  flip retire : UInt<1>, custom_mrw_csrs : UInt<64>[0],  flip cause : UInt<64>,  flip pc : UInt<40>,  flip badaddr : UInt<40>, fatc : UInt<1>, time : UInt<64>, fcsr_rm : UInt<3>,  flip fcsr_flags : {valid : UInt<1>, bits_wky : UInt<5>},  flip rocc_interrupt : UInt<1>, interrupt : UInt<1>, interrupt_cause : UInt<64>, bp : {control : {ttype : UInt<4>, dmode : UInt<1>, maskmax : UInt<6>, reserved : UInt<40>, action : UInt<1>, chain : UInt<1>, zero : UInt<2>, tmatch : UInt<2>, m : UInt<1>, h : UInt<1>, s : UInt<1>, u : UInt<1>, x : UInt<1>, w : UInt<1>, r : UInt<1>}, address : UInt<39>}[1], counters : {eventSel : UInt<64>,  flip inc : UInt<1>}[0]}
    io is invalid
    io is invalid
    wire _T_347 : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}
    _T_347 is invalid
    wire _T_377 : UInt<99>
    _T_377 is invalid
    _T_377 <= UInt<1>(0)
    node _T_378 = bits(_T_377, 0, 0)
    _T_347.uie <= _T_378
    node _T_379 = bits(_T_377, 1, 1)
    _T_347.sie <= _T_379
    node _T_380 = bits(_T_377, 2, 2)
    _T_347.hie <= _T_380
    node _T_381 = bits(_T_377, 3, 3)
    _T_347.mie <= _T_381
    node _T_382 = bits(_T_377, 4, 4)
    _T_347.upie <= _T_382
    node _T_383 = bits(_T_377, 5, 5)
    _T_347.spie <= _T_383
    node _T_384 = bits(_T_377, 6, 6)
    _T_347.hpie <= _T_384
    node _T_385 = bits(_T_377, 7, 7)
    _T_347.mpie <= _T_385
    node _T_386 = bits(_T_377, 8, 8)
    _T_347.spp <= _T_386
    node _T_387 = bits(_T_377, 10, 9)
    _T_347.hpp <= _T_387
    node _T_388 = bits(_T_377, 12, 11)
    _T_347.mpp <= _T_388
    node _T_389 = bits(_T_377, 14, 13)
    _T_347.fs <= _T_389
    node _T_390 = bits(_T_377, 16, 15)
    _T_347.xs <= _T_390
    node _T_391 = bits(_T_377, 17, 17)
    _T_347.mprv <= _T_391
    node _T_392 = bits(_T_377, 18, 18)
    _T_347.pum <= _T_392
    node _T_393 = bits(_T_377, 19, 19)
    _T_347.mxr <= _T_393
    node _T_394 = bits(_T_377, 20, 20)
    _T_347.tvm <= _T_394
    node _T_395 = bits(_T_377, 21, 21)
    _T_347.tw <= _T_395
    node _T_396 = bits(_T_377, 22, 22)
    _T_347.tsr <= _T_396
    node _T_397 = bits(_T_377, 30, 23)
    _T_347.zero1 <= _T_397
    node _T_398 = bits(_T_377, 31, 31)
    _T_347.sd_rv32 <= _T_398
    node _T_399 = bits(_T_377, 33, 32)
    _T_347.uxl <= _T_399
    node _T_400 = bits(_T_377, 35, 34)
    _T_347.sxl <= _T_400
    node _T_401 = bits(_T_377, 62, 36)
    _T_347.zero2 <= _T_401
    node _T_402 = bits(_T_377, 63, 63)
    _T_347.sd <= _T_402
    node _T_403 = bits(_T_377, 65, 64)
    _T_347.prv <= _T_403
    node _T_404 = bits(_T_377, 97, 66)
    _T_347.isa <= _T_404
    node _T_405 = bits(_T_377, 98, 98)
    _T_347.debug <= _T_405
    wire reset_mstatus : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}
    reset_mstatus is invalid
    reset_mstatus <= _T_347
    reset_mstatus.mpp <= UInt<2>(3)
    reset_mstatus.prv <= UInt<2>(3)
    regreset reg_mstatus : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}, clock, reset_wky, reset_mstatus
    wire new_prv : UInt<2>
    new_prv is invalid
    new_prv <= reg_mstatus.prv
    node _T_465 = eq(new_prv, UInt<2>(2))
    node _T_467 = mux(_T_465, UInt<1>(0), new_prv)
    reg_mstatus.prv <= _T_467
    wire _T_505 : {xdebugver : UInt<2>, ndreset : UInt<1>, fullreset : UInt<1>, zero3 : UInt<12>, ebreakm : UInt<1>, ebreakh : UInt<1>, ebreaks : UInt<1>, ebreaku : UInt<1>, zero2 : UInt<1>, stopcycle : UInt<1>, stoptime : UInt<1>, cause : UInt<3>, debugint : UInt<1>, zero1 : UInt<1>, halt : UInt<1>, step : UInt<1>, prv : UInt<2>}
    _T_505 is invalid
    wire _T_524 : UInt<32>
    _T_524 is invalid
    _T_524 <= UInt<1>(0)
    node _T_525 = bits(_T_524, 1, 0)
    _T_505.prv <= _T_525
    node _T_526 = bits(_T_524, 2, 2)
    _T_505.step <= _T_526
    node _T_527 = bits(_T_524, 3, 3)
    _T_505.halt <= _T_527
    node _T_528 = bits(_T_524, 4, 4)
    _T_505.zero1 <= _T_528
    node _T_529 = bits(_T_524, 5, 5)
    _T_505.debugint <= _T_529
    node _T_530 = bits(_T_524, 8, 6)
    _T_505.cause <= _T_530
    node _T_531 = bits(_T_524, 9, 9)
    _T_505.stoptime <= _T_531
    node _T_532 = bits(_T_524, 10, 10)
    _T_505.stopcycle <= _T_532
    node _T_533 = bits(_T_524, 11, 11)
    _T_505.zero2 <= _T_533
    node _T_534 = bits(_T_524, 12, 12)
    _T_505.ebreaku <= _T_534
    node _T_535 = bits(_T_524, 13, 13)
    _T_505.ebreaks <= _T_535
    node _T_536 = bits(_T_524, 14, 14)
    _T_505.ebreakh <= _T_536
    node _T_537 = bits(_T_524, 15, 15)
    _T_505.ebreakm <= _T_537
    node _T_538 = bits(_T_524, 27, 16)
    _T_505.zero3 <= _T_538
    node _T_539 = bits(_T_524, 28, 28)
    _T_505.fullreset <= _T_539
    node _T_540 = bits(_T_524, 29, 29)
    _T_505.ndreset <= _T_540
    node _T_541 = bits(_T_524, 31, 30)
    _T_505.xdebugver <= _T_541
    wire reset_dcsr : {xdebugver : UInt<2>, ndreset : UInt<1>, fullreset : UInt<1>, zero3 : UInt<12>, ebreakm : UInt<1>, ebreakh : UInt<1>, ebreaks : UInt<1>, ebreaku : UInt<1>, zero2 : UInt<1>, stopcycle : UInt<1>, stoptime : UInt<1>, cause : UInt<3>, debugint : UInt<1>, zero1 : UInt<1>, halt : UInt<1>, step : UInt<1>, prv : UInt<2>}
    reset_dcsr is invalid
    reset_dcsr <= _T_505
    reset_dcsr.xdebugver <= UInt<1>(1)
    reset_dcsr.prv <= UInt<2>(3)
    regreset reg_dcsr : {xdebugver : UInt<2>, ndreset : UInt<1>, fullreset : UInt<1>, zero3 : UInt<12>, ebreakm : UInt<1>, ebreakh : UInt<1>, ebreaks : UInt<1>, ebreaku : UInt<1>, zero2 : UInt<1>, stopcycle : UInt<1>, stoptime : UInt<1>, cause : UInt<3>, debugint : UInt<1>, zero1 : UInt<1>, halt : UInt<1>, step : UInt<1>, prv : UInt<2>}, clock, reset_wky, reset_dcsr
    wire _T_607 : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
    _T_607 is invalid
    wire _T_622 : UInt<13>
    _T_622 is invalid
    _T_622 <= UInt<1>(0)
    node _T_623 = bits(_T_622, 0, 0)
    _T_607.usip <= _T_623
    node _T_624 = bits(_T_622, 1, 1)
    _T_607.ssip <= _T_624
    node _T_625 = bits(_T_622, 2, 2)
    _T_607.hsip <= _T_625
    node _T_626 = bits(_T_622, 3, 3)
    _T_607.msip <= _T_626
    node _T_627 = bits(_T_622, 4, 4)
    _T_607.utip <= _T_627
    node _T_628 = bits(_T_622, 5, 5)
    _T_607.stip <= _T_628
    node _T_629 = bits(_T_622, 6, 6)
    _T_607.htip <= _T_629
    node _T_630 = bits(_T_622, 7, 7)
    _T_607.mtip <= _T_630
    node _T_631 = bits(_T_622, 8, 8)
    _T_607.ueip <= _T_631
    node _T_632 = bits(_T_622, 9, 9)
    _T_607.seip <= _T_632
    node _T_633 = bits(_T_622, 10, 10)
    _T_607.heip <= _T_633
    node _T_634 = bits(_T_622, 11, 11)
    _T_607.meip <= _T_634
    node _T_635 = bits(_T_622, 12, 12)
    _T_607.rocc <= _T_635
    wire _T_636 : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
    _T_636 is invalid
    _T_636 <= _T_607
    _T_636.ssip <= UInt<1>(1)
    _T_636.msip <= UInt<1>(1)
    _T_636.stip <= UInt<1>(1)
    _T_636.mtip <= UInt<1>(1)
    _T_636.meip <= UInt<1>(1)
    _T_636.seip <= UInt<1>(1)
    _T_636.rocc <= UInt<1>(0)
    wire _T_657 : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
    _T_657 is invalid
    _T_657 <= _T_636
    _T_657.msip <= UInt<1>(0)
    _T_657.mtip <= UInt<1>(0)
    _T_657.meip <= UInt<1>(0)
    node _T_674 = cat(_T_636.hsip, _T_636.ssip)
    node _T_675 = cat(_T_674, _T_636.usip)
    node _T_676 = cat(_T_636.stip, _T_636.utip)
    node _T_677 = cat(_T_676, _T_636.msip)
    node _T_678 = cat(_T_677, _T_675)
    node _T_679 = cat(_T_636.ueip, _T_636.mtip)
    node _T_680 = cat(_T_679, _T_636.htip)
    node _T_681 = cat(_T_636.heip, _T_636.seip)
    node _T_682 = cat(_T_636.rocc, _T_636.meip)
    node _T_683 = cat(_T_682, _T_681)
    node _T_684 = cat(_T_683, _T_680)
    node supported_interrupts = cat(_T_684, _T_678)
    node _T_685 = cat(_T_657.hsip, _T_657.ssip)
    node _T_686 = cat(_T_685, _T_657.usip)
    node _T_687 = cat(_T_657.stip, _T_657.utip)
    node _T_688 = cat(_T_687, _T_657.msip)
    node _T_689 = cat(_T_688, _T_686)
    node _T_690 = cat(_T_657.ueip, _T_657.mtip)
    node _T_691 = cat(_T_690, _T_657.htip)
    node _T_692 = cat(_T_657.heip, _T_657.seip)
    node _T_693 = cat(_T_657.rocc, _T_657.meip)
    node _T_694 = cat(_T_693, _T_692)
    node _T_695 = cat(_T_694, _T_691)
    node delegable_interrupts = cat(_T_695, _T_689)
    regreset reg_debug : UInt<1>, clock, reset_wky, UInt<1>(0)
    node effective_prv = cat(reg_debug, reg_mstatus.prv)
    reg reg_dpc : UInt<40>, clock 
    reg reg_dscratch : UInt<64>, clock 
    reg reg_singleStepped : UInt<1>, clock 
    reg reg_tselect : UInt<1>, clock 
    reg reg_bp : {control : {ttype : UInt<4>, dmode : UInt<1>, maskmax : UInt<6>, reserved : UInt<40>, action : UInt<1>, chain : UInt<1>, zero : UInt<2>, tmatch : UInt<2>, m : UInt<1>, h : UInt<1>, s : UInt<1>, u : UInt<1>, x : UInt<1>, w : UInt<1>, r : UInt<1>}, address : UInt<39>}[2], clock 
    reg reg_mie : UInt<64>, clock 
    reg reg_mideleg : UInt<64>, clock 
    reg reg_medeleg : UInt<64>, clock 
    reg reg_mip : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}, clock 
    reg reg_mepc : UInt<40>, clock 
    reg reg_mcause : UInt<64>, clock 
    reg reg_mbadaddr : UInt<40>, clock 
    reg reg_mscratch : UInt<64>, clock 
    regreset reg_mtvec : UInt<32>, clock, reset_wky, UInt<32>(0)
    reg reg_mcounteren : UInt<32>, clock 
    reg reg_scounteren : UInt<32>, clock 
    reg reg_sepc : UInt<40>, clock 
    reg reg_scause : UInt<64>, clock 
    reg reg_sbadaddr : UInt<40>, clock 
    reg reg_sscratch : UInt<64>, clock 
    reg reg_stvec : UInt<39>, clock 
    reg reg_sptbr : {mode : UInt<4>, asid : UInt<16>, ppn : UInt<44>}, clock 
    regreset reg_wfi : UInt<1>, clock, reset_wky, UInt<1>(0)
    reg reg_fflags : UInt<5>, clock 
    reg reg_frm : UInt<3>, clock 
    regreset _T_931 : UInt<6>, clock, reset_wky, UInt<6>(0)
    node _T_932 = add(_T_931, io.retire)
    _T_931 <= _T_932
    regreset _T_934 : UInt<58>, clock, reset_wky, UInt<58>(0)
    node _T_935 = bits(_T_932, 6, 6)
    when _T_935 : 
{
      node _T_937 = add(_T_934, UInt<1>(1))
      node _T_938 = tail(_T_937, 1)
      _T_934 <= _T_938
      skip
}
    node _T_939 = cat(_T_934, _T_931)
    regreset _T_942 : UInt<6>, clock, reset_wky, UInt<6>(0)
    node _T_943 = add(_T_942, UInt<1>(1))
    _T_942 <= _T_943
    regreset _T_945 : UInt<58>, clock, reset_wky, UInt<58>(0)
    node _T_946 = bits(_T_943, 6, 6)
    when _T_946 : 
{
      node _T_948 = add(_T_945, UInt<1>(1))
      node _T_949 = tail(_T_948, 1)
      _T_945 <= _T_949
      skip
}
    node _T_950 = cat(_T_945, _T_942)
    node _T_953 = eq(reg_mstatus.prv, UInt<1>(1))
    node _T_954 = or(UInt<1>(0), _T_953)
    node _T_956 = mux(_T_954, UInt<3>(7), reg_scounteren)
    node hpm_mask = and(reg_mcounteren, _T_956)
    wire mip : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
    mip is invalid
    mip <= reg_mip
    mip.rocc <= io.rocc_interrupt
    node _T_970 = cat(mip.hsip, mip.ssip)
    node _T_971 = cat(_T_970, mip.usip)
    node _T_972 = cat(mip.stip, mip.utip)
    node _T_973 = cat(_T_972, mip.msip)
    node _T_974 = cat(_T_973, _T_971)
    node _T_975 = cat(mip.ueip, mip.mtip)
    node _T_976 = cat(_T_975, mip.htip)
    node _T_977 = cat(mip.heip, mip.seip)
    node _T_978 = cat(mip.rocc, mip.meip)
    node _T_979 = cat(_T_978, _T_977)
    node _T_980 = cat(_T_979, _T_976)
    node _T_981 = cat(_T_980, _T_974)
    node read_mip = and(_T_981, supported_interrupts)
    node pending_interrupts = and(read_mip, reg_mie)
    node _T_983 = leq(reg_mstatus.prv, UInt<1>(1))
    node _T_985 = eq(reg_mstatus.prv, UInt<2>(3))
    node _T_986 = and(_T_985, reg_mstatus.mie)
    node _T_987 = or(_T_983, _T_986)
    node _T_988 = not(reg_mideleg)
    node _T_989 = and(pending_interrupts, _T_988)
    node m_interrupts = mux(_T_987, _T_989, UInt<1>(0))
    node _T_992 = eq(m_interrupts, UInt<1>(0))
    node _T_994 = lt(reg_mstatus.prv, UInt<1>(1))
    node _T_996 = eq(reg_mstatus.prv, UInt<1>(1))
    node _T_997 = and(_T_996, reg_mstatus.sie)
    node _T_998 = or(_T_994, _T_997)
    node _T_999 = and(_T_992, _T_998)
    node _T_1000 = and(pending_interrupts, reg_mideleg)
    node s_interrupts = mux(_T_999, _T_1000, UInt<1>(0))
    node all_interrupts = or(m_interrupts, s_interrupts)
    node _T_1003 = bits(all_interrupts, 0, 0)
    node _T_1004 = bits(all_interrupts, 1, 1)
    node _T_1005 = bits(all_interrupts, 2, 2)
    node _T_1006 = bits(all_interrupts, 3, 3)
    node _T_1007 = bits(all_interrupts, 4, 4)
    node _T_1008 = bits(all_interrupts, 5, 5)
    node _T_1009 = bits(all_interrupts, 6, 6)
    node _T_1010 = bits(all_interrupts, 7, 7)
    node _T_1011 = bits(all_interrupts, 8, 8)
    node _T_1012 = bits(all_interrupts, 9, 9)
    node _T_1013 = bits(all_interrupts, 10, 10)
    node _T_1014 = bits(all_interrupts, 11, 11)
    node _T_1015 = bits(all_interrupts, 12, 12)
    node _T_1016 = bits(all_interrupts, 13, 13)
    node _T_1017 = bits(all_interrupts, 14, 14)
    node _T_1018 = bits(all_interrupts, 15, 15)
    node _T_1019 = bits(all_interrupts, 16, 16)
    node _T_1020 = bits(all_interrupts, 17, 17)
    node _T_1021 = bits(all_interrupts, 18, 18)
    node _T_1022 = bits(all_interrupts, 19, 19)
    node _T_1023 = bits(all_interrupts, 20, 20)
    node _T_1024 = bits(all_interrupts, 21, 21)
    node _T_1025 = bits(all_interrupts, 22, 22)
    node _T_1026 = bits(all_interrupts, 23, 23)
    node _T_1027 = bits(all_interrupts, 24, 24)
    node _T_1028 = bits(all_interrupts, 25, 25)
    node _T_1029 = bits(all_interrupts, 26, 26)
    node _T_1030 = bits(all_interrupts, 27, 27)
    node _T_1031 = bits(all_interrupts, 28, 28)
    node _T_1032 = bits(all_interrupts, 29, 29)
    node _T_1033 = bits(all_interrupts, 30, 30)
    node _T_1034 = bits(all_interrupts, 31, 31)
    node _T_1035 = bits(all_interrupts, 32, 32)
    node _T_1036 = bits(all_interrupts, 33, 33)
    node _T_1037 = bits(all_interrupts, 34, 34)
    node _T_1038 = bits(all_interrupts, 35, 35)
    node _T_1039 = bits(all_interrupts, 36, 36)
    node _T_1040 = bits(all_interrupts, 37, 37)
    node _T_1041 = bits(all_interrupts, 38, 38)
    node _T_1042 = bits(all_interrupts, 39, 39)
    node _T_1043 = bits(all_interrupts, 40, 40)
    node _T_1044 = bits(all_interrupts, 41, 41)
    node _T_1045 = bits(all_interrupts, 42, 42)
    node _T_1046 = bits(all_interrupts, 43, 43)
    node _T_1047 = bits(all_interrupts, 44, 44)
    node _T_1048 = bits(all_interrupts, 45, 45)
    node _T_1049 = bits(all_interrupts, 46, 46)
    node _T_1050 = bits(all_interrupts, 47, 47)
    node _T_1051 = bits(all_interrupts, 48, 48)
    node _T_1052 = bits(all_interrupts, 49, 49)
    node _T_1053 = bits(all_interrupts, 50, 50)
    node _T_1054 = bits(all_interrupts, 51, 51)
    node _T_1055 = bits(all_interrupts, 52, 52)
    node _T_1056 = bits(all_interrupts, 53, 53)
    node _T_1057 = bits(all_interrupts, 54, 54)
    node _T_1058 = bits(all_interrupts, 55, 55)
    node _T_1059 = bits(all_interrupts, 56, 56)
    node _T_1060 = bits(all_interrupts, 57, 57)
    node _T_1061 = bits(all_interrupts, 58, 58)
    node _T_1062 = bits(all_interrupts, 59, 59)
    node _T_1063 = bits(all_interrupts, 60, 60)
    node _T_1064 = bits(all_interrupts, 61, 61)
    node _T_1065 = bits(all_interrupts, 62, 62)
    node _T_1066 = bits(all_interrupts, 63, 63)
    node _T_1131 = mux(_T_1065, UInt<6>(62), UInt<6>(63))
    node _T_1132 = mux(_T_1064, UInt<6>(61), _T_1131)
    node _T_1133 = mux(_T_1063, UInt<6>(60), _T_1132)
    node _T_1134 = mux(_T_1062, UInt<6>(59), _T_1133)
    node _T_1135 = mux(_T_1061, UInt<6>(58), _T_1134)
    node _T_1136 = mux(_T_1060, UInt<6>(57), _T_1135)
    node _T_1137 = mux(_T_1059, UInt<6>(56), _T_1136)
    node _T_1138 = mux(_T_1058, UInt<6>(55), _T_1137)
    node _T_1139 = mux(_T_1057, UInt<6>(54), _T_1138)
    node _T_1140 = mux(_T_1056, UInt<6>(53), _T_1139)
    node _T_1141 = mux(_T_1055, UInt<6>(52), _T_1140)
    node _T_1142 = mux(_T_1054, UInt<6>(51), _T_1141)
    node _T_1143 = mux(_T_1053, UInt<6>(50), _T_1142)
    node _T_1144 = mux(_T_1052, UInt<6>(49), _T_1143)
    node _T_1145 = mux(_T_1051, UInt<6>(48), _T_1144)
    node _T_1146 = mux(_T_1050, UInt<6>(47), _T_1145)
    node _T_1147 = mux(_T_1049, UInt<6>(46), _T_1146)
    node _T_1148 = mux(_T_1048, UInt<6>(45), _T_1147)
    node _T_1149 = mux(_T_1047, UInt<6>(44), _T_1148)
    node _T_1150 = mux(_T_1046, UInt<6>(43), _T_1149)
    node _T_1151 = mux(_T_1045, UInt<6>(42), _T_1150)
    node _T_1152 = mux(_T_1044, UInt<6>(41), _T_1151)
    node _T_1153 = mux(_T_1043, UInt<6>(40), _T_1152)
    node _T_1154 = mux(_T_1042, UInt<6>(39), _T_1153)
    node _T_1155 = mux(_T_1041, UInt<6>(38), _T_1154)
    node _T_1156 = mux(_T_1040, UInt<6>(37), _T_1155)
    node _T_1157 = mux(_T_1039, UInt<6>(36), _T_1156)
    node _T_1158 = mux(_T_1038, UInt<6>(35), _T_1157)
    node _T_1159 = mux(_T_1037, UInt<6>(34), _T_1158)
    node _T_1160 = mux(_T_1036, UInt<6>(33), _T_1159)
    node _T_1161 = mux(_T_1035, UInt<6>(32), _T_1160)
    node _T_1162 = mux(_T_1034, UInt<5>(31), _T_1161)
    node _T_1163 = mux(_T_1033, UInt<5>(30), _T_1162)
    node _T_1164 = mux(_T_1032, UInt<5>(29), _T_1163)
    node _T_1165 = mux(_T_1031, UInt<5>(28), _T_1164)
    node _T_1166 = mux(_T_1030, UInt<5>(27), _T_1165)
    node _T_1167 = mux(_T_1029, UInt<5>(26), _T_1166)
    node _T_1168 = mux(_T_1028, UInt<5>(25), _T_1167)
    node _T_1169 = mux(_T_1027, UInt<5>(24), _T_1168)
    node _T_1170 = mux(_T_1026, UInt<5>(23), _T_1169)
    node _T_1171 = mux(_T_1025, UInt<5>(22), _T_1170)
    node _T_1172 = mux(_T_1024, UInt<5>(21), _T_1171)
    node _T_1173 = mux(_T_1023, UInt<5>(20), _T_1172)
    node _T_1174 = mux(_T_1022, UInt<5>(19), _T_1173)
    node _T_1175 = mux(_T_1021, UInt<5>(18), _T_1174)
    node _T_1176 = mux(_T_1020, UInt<5>(17), _T_1175)
    node _T_1177 = mux(_T_1019, UInt<5>(16), _T_1176)
    node _T_1178 = mux(_T_1018, UInt<4>(15), _T_1177)
    node _T_1179 = mux(_T_1017, UInt<4>(14), _T_1178)
    node _T_1180 = mux(_T_1016, UInt<4>(13), _T_1179)
    node _T_1181 = mux(_T_1015, UInt<4>(12), _T_1180)
    node _T_1182 = mux(_T_1014, UInt<4>(11), _T_1181)
    node _T_1183 = mux(_T_1013, UInt<4>(10), _T_1182)
    node _T_1184 = mux(_T_1012, UInt<4>(9), _T_1183)
    node _T_1185 = mux(_T_1011, UInt<4>(8), _T_1184)
    node _T_1186 = mux(_T_1010, UInt<3>(7), _T_1185)
    node _T_1187 = mux(_T_1009, UInt<3>(6), _T_1186)
    node _T_1188 = mux(_T_1008, UInt<3>(5), _T_1187)
    node _T_1189 = mux(_T_1007, UInt<3>(4), _T_1188)
    node _T_1190 = mux(_T_1006, UInt<2>(3), _T_1189)
    node _T_1191 = mux(_T_1005, UInt<2>(2), _T_1190)
    node _T_1192 = mux(_T_1004, UInt<1>(1), _T_1191)
    node _T_1193 = mux(_T_1003, UInt<1>(0), _T_1192)
    node _T_1194 = add(UInt<64>(9223372036854775808), _T_1193)
    node interruptCause = tail(_T_1194, 1)
    node _T_1196 = neq(all_interrupts, UInt<1>(0))
    node _T_1198 = eq(reg_debug, UInt<1>(0))
    node _T_1199 = and(_T_1196, _T_1198)
    node _T_1201 = eq(io.singleStep, UInt<1>(0))
    node _T_1202 = and(_T_1199, _T_1201)
    node _T_1203 = or(_T_1202, reg_singleStepped)
    io.interrupt <= _T_1203
    io.interrupt_cause <= interruptCause
    io.bp[0] <= reg_bp[0]
    node _T_1205 = and(UInt<1>(1), reg_dcsr.debugint)
    node _T_1207 = eq(reg_debug, UInt<1>(0))
    node _T_1208 = and(_T_1205, _T_1207)
    when _T_1208 : 
{
      io.interrupt <= UInt<1>(1)
      node _T_1226 = add(UInt<64>(9223372036854775808), UInt<4>(13))
      node _T_1227 = tail(_T_1226, 1)
      io.interrupt_cause <= _T_1227
      skip
}
    regreset reg_misa : UInt<64>, clock, reset_wky, UInt<64>(9223372036856090925)
    node _T_1229 = cat(io.status.hie, io.status.sie)
    node _T_1230 = cat(_T_1229, io.status.uie)
    node _T_1231 = cat(io.status.upie, io.status.mie)
    node _T_1232 = cat(io.status.hpie, io.status.spie)
    node _T_1233 = cat(_T_1232, _T_1231)
    node _T_1234 = cat(_T_1233, _T_1230)
    node _T_1235 = cat(io.status.hpp, io.status.spp)
    node _T_1236 = cat(_T_1235, io.status.mpie)
    node _T_1237 = cat(io.status.fs, io.status.mpp)
    node _T_1238 = cat(io.status.mprv, io.status.xs)
    node _T_1239 = cat(_T_1238, _T_1237)
    node _T_1240 = cat(_T_1239, _T_1236)
    node _T_1241 = cat(_T_1240, _T_1234)
    node _T_1242 = cat(io.status.tvm, io.status.mxr)
    node _T_1243 = cat(_T_1242, io.status.pum)
    node _T_1244 = cat(io.status.tsr, io.status.tw)
    node _T_1245 = cat(io.status.sd_rv32, io.status.zero1)
    node _T_1246 = cat(_T_1245, _T_1244)
    node _T_1247 = cat(_T_1246, _T_1243)
    node _T_1248 = cat(io.status.zero2, io.status.sxl)
    node _T_1249 = cat(_T_1248, io.status.uxl)
    node _T_1250 = cat(io.status.prv, io.status.sd)
    node _T_1251 = cat(io.status.debug, io.status.isa)
    node _T_1252 = cat(_T_1251, _T_1250)
    node _T_1253 = cat(_T_1252, _T_1249)
    node _T_1254 = cat(_T_1253, _T_1247)
    node _T_1255 = cat(_T_1254, _T_1241)
    node read_mstatus = bits(_T_1255, 63, 0)
    node _T_1291 = cat(reg_bp[reg_tselect].control.x, reg_bp[reg_tselect].control.w)
    node _T_1292 = cat(_T_1291, reg_bp[reg_tselect].control.r)
    node _T_1293 = cat(reg_bp[reg_tselect].control.s, reg_bp[reg_tselect].control.u)
    node _T_1294 = cat(reg_bp[reg_tselect].control.m, reg_bp[reg_tselect].control.h)
    node _T_1295 = cat(_T_1294, _T_1293)
    node _T_1296 = cat(_T_1295, _T_1292)
    node _T_1297 = cat(reg_bp[reg_tselect].control.zero, reg_bp[reg_tselect].control.tmatch)
    node _T_1298 = cat(reg_bp[reg_tselect].control.action, reg_bp[reg_tselect].control.chain)
    node _T_1299 = cat(_T_1298, _T_1297)
    node _T_1300 = cat(reg_bp[reg_tselect].control.maskmax, reg_bp[reg_tselect].control.reserved)
    node _T_1301 = cat(reg_bp[reg_tselect].control.ttype, reg_bp[reg_tselect].control.dmode)
    node _T_1302 = cat(_T_1301, _T_1300)
    node _T_1303 = cat(_T_1302, _T_1299)
    node _T_1304 = cat(_T_1303, _T_1296)
    node _T_1340 = bits(reg_bp[reg_tselect].address, 38, 38)
    node _T_1341 = bits(_T_1340, 0, 0)
    node _T_1344 = mux(_T_1341, UInt<25>(33554431), UInt<25>(0))
    node _T_1345 = cat(_T_1344, reg_bp[reg_tselect].address)
    node _T_1349 = bits(reg_mepc, 39, 39)
    node _T_1350 = bits(_T_1349, 0, 0)
    node _T_1353 = mux(_T_1350, UInt<24>(16777215), UInt<24>(0))
    node _T_1354 = cat(_T_1353, reg_mepc)
    node _T_1355 = bits(reg_mbadaddr, 39, 39)
    node _T_1356 = bits(_T_1355, 0, 0)
    node _T_1359 = mux(_T_1356, UInt<24>(16777215), UInt<24>(0))
    node _T_1360 = cat(_T_1359, reg_mbadaddr)
    node _T_1361 = cat(reg_dcsr.step, reg_dcsr.prv)
    node _T_1362 = cat(reg_dcsr.zero1, reg_dcsr.halt)
    node _T_1363 = cat(_T_1362, _T_1361)
    node _T_1364 = cat(reg_dcsr.cause, reg_dcsr.debugint)
    node _T_1365 = cat(reg_dcsr.stopcycle, reg_dcsr.stoptime)
    node _T_1366 = cat(_T_1365, _T_1364)
    node _T_1367 = cat(_T_1366, _T_1363)
    node _T_1368 = cat(reg_dcsr.ebreaku, reg_dcsr.zero2)
    node _T_1369 = cat(reg_dcsr.ebreakh, reg_dcsr.ebreaks)
    node _T_1370 = cat(_T_1369, _T_1368)
    node _T_1371 = cat(reg_dcsr.zero3, reg_dcsr.ebreakm)
    node _T_1372 = cat(reg_dcsr.xdebugver, reg_dcsr.ndreset)
    node _T_1373 = cat(_T_1372, reg_dcsr.fullreset)
    node _T_1374 = cat(_T_1373, _T_1371)
    node _T_1375 = cat(_T_1374, _T_1370)
    node _T_1376 = cat(_T_1375, _T_1367)
    node _T_1377 = cat(reg_frm, reg_fflags)
    node _T_1380 = and(reg_mie, reg_mideleg)
    node _T_1381 = and(read_mip, reg_mideleg)
    wire _T_1382 : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}
    _T_1382 is invalid
    _T_1382 <= io.status
    _T_1382.mprv <= UInt<1>(0)
    _T_1382.mpp <= UInt<1>(0)
    _T_1382.hpp <= UInt<1>(0)
    _T_1382.mpie <= UInt<1>(0)
    _T_1382.hpie <= UInt<1>(0)
    _T_1382.mie <= UInt<1>(0)
    _T_1382.hie <= UInt<1>(0)
    node _T_1418 = cat(_T_1382.hie, _T_1382.sie)
    node _T_1419 = cat(_T_1418, _T_1382.uie)
    node _T_1420 = cat(_T_1382.upie, _T_1382.mie)
    node _T_1421 = cat(_T_1382.hpie, _T_1382.spie)
    node _T_1422 = cat(_T_1421, _T_1420)
    node _T_1423 = cat(_T_1422, _T_1419)
    node _T_1424 = cat(_T_1382.hpp, _T_1382.spp)
    node _T_1425 = cat(_T_1424, _T_1382.mpie)
    node _T_1426 = cat(_T_1382.fs, _T_1382.mpp)
    node _T_1427 = cat(_T_1382.mprv, _T_1382.xs)
    node _T_1428 = cat(_T_1427, _T_1426)
    node _T_1429 = cat(_T_1428, _T_1425)
    node _T_1430 = cat(_T_1429, _T_1423)
    node _T_1431 = cat(_T_1382.tvm, _T_1382.mxr)
    node _T_1432 = cat(_T_1431, _T_1382.pum)
    node _T_1433 = cat(_T_1382.tsr, _T_1382.tw)
    node _T_1434 = cat(_T_1382.sd_rv32, _T_1382.zero1)
    node _T_1435 = cat(_T_1434, _T_1433)
    node _T_1436 = cat(_T_1435, _T_1432)
    node _T_1437 = cat(_T_1382.zero2, _T_1382.sxl)
    node _T_1438 = cat(_T_1437, _T_1382.uxl)
    node _T_1439 = cat(_T_1382.prv, _T_1382.sd)
    node _T_1440 = cat(_T_1382.debug, _T_1382.isa)
    node _T_1441 = cat(_T_1440, _T_1439)
    node _T_1442 = cat(_T_1441, _T_1438)
    node _T_1443 = cat(_T_1442, _T_1436)
    node _T_1444 = cat(_T_1443, _T_1430)
    node _T_1445 = bits(_T_1444, 63, 0)
    node _T_1446 = bits(reg_sbadaddr, 39, 39)
    node _T_1447 = bits(_T_1446, 0, 0)
    node _T_1450 = mux(_T_1447, UInt<24>(16777215), UInt<24>(0))
    node _T_1451 = cat(_T_1450, reg_sbadaddr)
    node _T_1452 = cat(reg_sptbr.mode, reg_sptbr.asid)
    node _T_1453 = cat(_T_1452, reg_sptbr.ppn)
    node _T_1454 = bits(reg_sepc, 39, 39)
    node _T_1455 = bits(_T_1454, 0, 0)
    node _T_1458 = mux(_T_1455, UInt<24>(16777215), UInt<24>(0))
    node _T_1459 = cat(_T_1458, reg_sepc)
    node _T_1460 = bits(reg_stvec, 38, 38)
    node _T_1461 = bits(_T_1460, 0, 0)
    node _T_1464 = mux(_T_1461, UInt<25>(33554431), UInt<25>(0))
    node _T_1465 = cat(_T_1464, reg_stvec)
    node _T_1467 = eq(io.rw.addr, UInt<11>(1952))
    node _T_1469 = eq(io.rw.addr, UInt<11>(1953))
    node _T_1471 = eq(io.rw.addr, UInt<11>(1954))
    node _T_1473 = eq(io.rw.addr, UInt<12>(3859))
    node _T_1475 = eq(io.rw.addr, UInt<12>(3858))
    node _T_1477 = eq(io.rw.addr, UInt<12>(3857))
    node _T_1479 = eq(io.rw.addr, UInt<12>(2816))
    node _T_1481 = eq(io.rw.addr, UInt<12>(2818))
    node _T_1483 = eq(io.rw.addr, UInt<10>(769))
    node _T_1485 = eq(io.rw.addr, UInt<10>(768))
    node _T_1487 = eq(io.rw.addr, UInt<10>(773))
    node _T_1489 = eq(io.rw.addr, UInt<10>(836))
    node _T_1491 = eq(io.rw.addr, UInt<10>(772))
    node _T_1493 = eq(io.rw.addr, UInt<10>(771))
    node _T_1495 = eq(io.rw.addr, UInt<10>(770))
    node _T_1497 = eq(io.rw.addr, UInt<10>(832))
    node _T_1499 = eq(io.rw.addr, UInt<10>(833))
    node _T_1501 = eq(io.rw.addr, UInt<10>(835))
    node _T_1503 = eq(io.rw.addr, UInt<10>(834))
    node _T_1505 = eq(io.rw.addr, UInt<12>(3860))
    node _T_1507 = eq(io.rw.addr, UInt<11>(1968))
    node _T_1509 = eq(io.rw.addr, UInt<11>(1969))
    node _T_1511 = eq(io.rw.addr, UInt<11>(1970))
    node _T_1513 = eq(io.rw.addr, UInt<1>(1))
    node _T_1515 = eq(io.rw.addr, UInt<2>(2))
    node _T_1517 = eq(io.rw.addr, UInt<2>(3))
    node _T_1519 = eq(io.rw.addr, UInt<10>(803))
    node _T_1521 = eq(io.rw.addr, UInt<12>(2819))
    node _T_1523 = eq(io.rw.addr, UInt<12>(3075))
    node _T_1525 = eq(io.rw.addr, UInt<10>(804))
    node _T_1527 = eq(io.rw.addr, UInt<12>(2820))
    node _T_1529 = eq(io.rw.addr, UInt<12>(3076))
    node _T_1531 = eq(io.rw.addr, UInt<10>(805))
    node _T_1533 = eq(io.rw.addr, UInt<12>(2821))
    node _T_1535 = eq(io.rw.addr, UInt<12>(3077))
    node _T_1537 = eq(io.rw.addr, UInt<10>(806))
    node _T_1539 = eq(io.rw.addr, UInt<12>(2822))
    node _T_1541 = eq(io.rw.addr, UInt<12>(3078))
    node _T_1543 = eq(io.rw.addr, UInt<10>(807))
    node _T_1545 = eq(io.rw.addr, UInt<12>(2823))
    node _T_1547 = eq(io.rw.addr, UInt<12>(3079))
    node _T_1549 = eq(io.rw.addr, UInt<10>(808))
    node _T_1551 = eq(io.rw.addr, UInt<12>(2824))
    node _T_1553 = eq(io.rw.addr, UInt<12>(3080))
    node _T_1555 = eq(io.rw.addr, UInt<10>(809))
    node _T_1557 = eq(io.rw.addr, UInt<12>(2825))
    node _T_1559 = eq(io.rw.addr, UInt<12>(3081))
    node _T_1561 = eq(io.rw.addr, UInt<10>(810))
    node _T_1563 = eq(io.rw.addr, UInt<12>(2826))
    node _T_1565 = eq(io.rw.addr, UInt<12>(3082))
    node _T_1567 = eq(io.rw.addr, UInt<10>(811))
    node _T_1569 = eq(io.rw.addr, UInt<12>(2827))
    node _T_1571 = eq(io.rw.addr, UInt<12>(3083))
    node _T_1573 = eq(io.rw.addr, UInt<10>(812))
    node _T_1575 = eq(io.rw.addr, UInt<12>(2828))
    node _T_1577 = eq(io.rw.addr, UInt<12>(3084))
    node _T_1579 = eq(io.rw.addr, UInt<10>(813))
    node _T_1581 = eq(io.rw.addr, UInt<12>(2829))
    node _T_1583 = eq(io.rw.addr, UInt<12>(3085))
    node _T_1585 = eq(io.rw.addr, UInt<10>(814))
    node _T_1587 = eq(io.rw.addr, UInt<12>(2830))
    node _T_1589 = eq(io.rw.addr, UInt<12>(3086))
    node _T_1591 = eq(io.rw.addr, UInt<10>(815))
    node _T_1593 = eq(io.rw.addr, UInt<12>(2831))
    node _T_1595 = eq(io.rw.addr, UInt<12>(3087))
    node _T_1597 = eq(io.rw.addr, UInt<10>(816))
    node _T_1599 = eq(io.rw.addr, UInt<12>(2832))
    node _T_1601 = eq(io.rw.addr, UInt<12>(3088))
    node _T_1603 = eq(io.rw.addr, UInt<10>(817))
    node _T_1605 = eq(io.rw.addr, UInt<12>(2833))
    node _T_1607 = eq(io.rw.addr, UInt<12>(3089))
    node _T_1609 = eq(io.rw.addr, UInt<10>(818))
    node _T_1611 = eq(io.rw.addr, UInt<12>(2834))
    node _T_1613 = eq(io.rw.addr, UInt<12>(3090))
    node _T_1615 = eq(io.rw.addr, UInt<10>(819))
    node _T_1617 = eq(io.rw.addr, UInt<12>(2835))
    node _T_1619 = eq(io.rw.addr, UInt<12>(3091))
    node _T_1621 = eq(io.rw.addr, UInt<10>(820))
    node _T_1623 = eq(io.rw.addr, UInt<12>(2836))
    node _T_1625 = eq(io.rw.addr, UInt<12>(3092))
    node _T_1627 = eq(io.rw.addr, UInt<10>(821))
    node _T_1629 = eq(io.rw.addr, UInt<12>(2837))
    node _T_1631 = eq(io.rw.addr, UInt<12>(3093))
    node _T_1633 = eq(io.rw.addr, UInt<10>(822))
    node _T_1635 = eq(io.rw.addr, UInt<12>(2838))
    node _T_1637 = eq(io.rw.addr, UInt<12>(3094))
    node _T_1639 = eq(io.rw.addr, UInt<10>(823))
    node _T_1641 = eq(io.rw.addr, UInt<12>(2839))
    node _T_1643 = eq(io.rw.addr, UInt<12>(3095))
    node _T_1645 = eq(io.rw.addr, UInt<10>(824))
    node _T_1647 = eq(io.rw.addr, UInt<12>(2840))
    node _T_1649 = eq(io.rw.addr, UInt<12>(3096))
    node _T_1651 = eq(io.rw.addr, UInt<10>(825))
    node _T_1653 = eq(io.rw.addr, UInt<12>(2841))
    node _T_1655 = eq(io.rw.addr, UInt<12>(3097))
    node _T_1657 = eq(io.rw.addr, UInt<10>(826))
    node _T_1659 = eq(io.rw.addr, UInt<12>(2842))
    node _T_1661 = eq(io.rw.addr, UInt<12>(3098))
    node _T_1663 = eq(io.rw.addr, UInt<10>(827))
    node _T_1665 = eq(io.rw.addr, UInt<12>(2843))
    node _T_1667 = eq(io.rw.addr, UInt<12>(3099))
    node _T_1669 = eq(io.rw.addr, UInt<10>(828))
    node _T_1671 = eq(io.rw.addr, UInt<12>(2844))
    node _T_1673 = eq(io.rw.addr, UInt<12>(3100))
    node _T_1675 = eq(io.rw.addr, UInt<10>(829))
    node _T_1677 = eq(io.rw.addr, UInt<12>(2845))
    node _T_1679 = eq(io.rw.addr, UInt<12>(3101))
    node _T_1681 = eq(io.rw.addr, UInt<10>(830))
    node _T_1683 = eq(io.rw.addr, UInt<12>(2846))
    node _T_1685 = eq(io.rw.addr, UInt<12>(3102))
    node _T_1687 = eq(io.rw.addr, UInt<10>(831))
    node _T_1689 = eq(io.rw.addr, UInt<12>(2847))
    node _T_1691 = eq(io.rw.addr, UInt<12>(3103))
    node _T_1693 = eq(io.rw.addr, UInt<9>(256))
    node _T_1695 = eq(io.rw.addr, UInt<9>(324))
    node _T_1697 = eq(io.rw.addr, UInt<9>(260))
    node _T_1699 = eq(io.rw.addr, UInt<9>(320))
    node _T_1701 = eq(io.rw.addr, UInt<9>(322))
    node _T_1703 = eq(io.rw.addr, UInt<9>(323))
    node _T_1705 = eq(io.rw.addr, UInt<9>(384))
    node _T_1707 = eq(io.rw.addr, UInt<9>(321))
    node _T_1709 = eq(io.rw.addr, UInt<9>(261))
    node _T_1711 = eq(io.rw.addr, UInt<9>(262))
    node _T_1713 = eq(io.rw.addr, UInt<10>(774))
    node _T_1715 = eq(io.rw.addr, UInt<12>(3072))
    node _T_1717 = eq(io.rw.addr, UInt<12>(3074))
    node _T_1720 = eq(io.rw.cmd, UInt<3>(2))
    node _T_1721 = eq(io.rw.cmd, UInt<3>(3))
    node _T_1722 = or(_T_1720, _T_1721)
    node _T_1724 = mux(_T_1722, io.rw.rdata, UInt<1>(0))
    node _T_1725 = or(_T_1724, io.rw.wdata)
    node _T_1727 = eq(io.rw.cmd, UInt<3>(3))
    node _T_1729 = mux(_T_1727, io.rw.wdata, UInt<1>(0))
    node _T_1730 = not(_T_1729)
    node wdata = and(_T_1725, _T_1730)
    node system_insn = eq(io.rw.cmd, UInt<3>(4))
    node _T_1733 = bits(io.rw.addr, 2, 0)
    node opcode = dshl(UInt<1>(1), _T_1733)
    node insn_rs2 = bits(io.rw.addr, 5, 5)
    node _T_1735 = eq(insn_rs2, UInt<1>(0))
    node _T_1736 = and(system_insn, _T_1735)
    node _T_1737 = bits(opcode, 0, 0)
    node insn_call = and(_T_1736, _T_1737)
    node _T_1738 = bits(opcode, 1, 1)
    node insn_break = and(system_insn, _T_1738)
    node _T_1739 = bits(opcode, 2, 2)
    node insn_ret = and(system_insn, _T_1739)
    node _T_1740 = bits(opcode, 5, 5)
    node insn_wfi = and(system_insn, _T_1740)
    node insn_sfence_vma = and(system_insn, insn_rs2)
    node _T_1743 = gt(effective_prv, UInt<1>(1))
    node _T_1744 = or(UInt<1>(0), _T_1743)
    node _T_1746 = eq(reg_mstatus.tw, UInt<1>(0))
    node allow_wfi = or(_T_1744, _T_1746)
    node _T_1749 = gt(effective_prv, UInt<1>(1))
    node _T_1750 = or(UInt<1>(0), _T_1749)
    node _T_1752 = eq(reg_mstatus.tvm, UInt<1>(0))
    node allow_sfence_vma = or(_T_1750, _T_1752)
    node _T_1755 = gt(effective_prv, UInt<1>(1))
    node _T_1756 = or(UInt<1>(0), _T_1755)
    node _T_1758 = eq(reg_mstatus.tsr, UInt<1>(0))
    node allow_sret = or(_T_1756, _T_1758)
    node _T_1760 = eq(io.status.fs, UInt<1>(0))
    node _T_1761 = bits(reg_misa, 5, 5)
    node _T_1763 = eq(_T_1761, UInt<1>(0))
    node _T_1764 = or(_T_1760, _T_1763)
    io.decode.fp_illegal <= _T_1764
    node _T_1766 = eq(io.status.xs, UInt<1>(0))
    node _T_1767 = bits(reg_misa, 23, 23)
    node _T_1769 = eq(_T_1767, UInt<1>(0))
    node _T_1770 = or(_T_1766, _T_1769)
    io.decode.rocc_illegal <= _T_1770
    node _T_1771 = bits(io.decode.csr, 9, 8)
    node _T_1772 = lt(effective_prv, _T_1771)
    node _T_1774 = eq(io.decode.csr, UInt<11>(1952))
    node _T_1776 = eq(io.decode.csr, UInt<11>(1953))
    node _T_1778 = eq(io.decode.csr, UInt<11>(1954))
    node _T_1780 = eq(io.decode.csr, UInt<12>(3859))
    node _T_1782 = eq(io.decode.csr, UInt<12>(3858))
    node _T_1784 = eq(io.decode.csr, UInt<12>(3857))
    node _T_1786 = eq(io.decode.csr, UInt<12>(2816))
    node _T_1788 = eq(io.decode.csr, UInt<12>(2818))
    node _T_1790 = eq(io.decode.csr, UInt<10>(769))
    node _T_1792 = eq(io.decode.csr, UInt<10>(768))
    node _T_1794 = eq(io.decode.csr, UInt<10>(773))
    node _T_1796 = eq(io.decode.csr, UInt<10>(836))
    node _T_1798 = eq(io.decode.csr, UInt<10>(772))
    node _T_1800 = eq(io.decode.csr, UInt<10>(771))
    node _T_1802 = eq(io.decode.csr, UInt<10>(770))
    node _T_1804 = eq(io.decode.csr, UInt<10>(832))
    node _T_1806 = eq(io.decode.csr, UInt<10>(833))
    node _T_1808 = eq(io.decode.csr, UInt<10>(835))
    node _T_1810 = eq(io.decode.csr, UInt<10>(834))
    node _T_1812 = eq(io.decode.csr, UInt<12>(3860))
    node _T_1814 = eq(io.decode.csr, UInt<11>(1968))
    node _T_1816 = eq(io.decode.csr, UInt<11>(1969))
    node _T_1818 = eq(io.decode.csr, UInt<11>(1970))
    node _T_1820 = eq(io.decode.csr, UInt<1>(1))
    node _T_1822 = eq(io.decode.csr, UInt<2>(2))
    node _T_1824 = eq(io.decode.csr, UInt<2>(3))
    node _T_1826 = eq(io.decode.csr, UInt<10>(803))
    node _T_1828 = eq(io.decode.csr, UInt<12>(2819))
    node _T_1830 = eq(io.decode.csr, UInt<12>(3075))
    node _T_1832 = eq(io.decode.csr, UInt<10>(804))
    node _T_1834 = eq(io.decode.csr, UInt<12>(2820))
    node _T_1836 = eq(io.decode.csr, UInt<12>(3076))
    node _T_1838 = eq(io.decode.csr, UInt<10>(805))
    node _T_1840 = eq(io.decode.csr, UInt<12>(2821))
    node _T_1842 = eq(io.decode.csr, UInt<12>(3077))
    node _T_1844 = eq(io.decode.csr, UInt<10>(806))
    node _T_1846 = eq(io.decode.csr, UInt<12>(2822))
    node _T_1848 = eq(io.decode.csr, UInt<12>(3078))
    node _T_1850 = eq(io.decode.csr, UInt<10>(807))
    node _T_1852 = eq(io.decode.csr, UInt<12>(2823))
    node _T_1854 = eq(io.decode.csr, UInt<12>(3079))
    node _T_1856 = eq(io.decode.csr, UInt<10>(808))
    node _T_1858 = eq(io.decode.csr, UInt<12>(2824))
    node _T_1860 = eq(io.decode.csr, UInt<12>(3080))
    node _T_1862 = eq(io.decode.csr, UInt<10>(809))
    node _T_1864 = eq(io.decode.csr, UInt<12>(2825))
    node _T_1866 = eq(io.decode.csr, UInt<12>(3081))
    node _T_1868 = eq(io.decode.csr, UInt<10>(810))
    node _T_1870 = eq(io.decode.csr, UInt<12>(2826))
    node _T_1872 = eq(io.decode.csr, UInt<12>(3082))
    node _T_1874 = eq(io.decode.csr, UInt<10>(811))
    node _T_1876 = eq(io.decode.csr, UInt<12>(2827))
    node _T_1878 = eq(io.decode.csr, UInt<12>(3083))
    node _T_1880 = eq(io.decode.csr, UInt<10>(812))
    node _T_1882 = eq(io.decode.csr, UInt<12>(2828))
    node _T_1884 = eq(io.decode.csr, UInt<12>(3084))
    node _T_1886 = eq(io.decode.csr, UInt<10>(813))
    node _T_1888 = eq(io.decode.csr, UInt<12>(2829))
    node _T_1890 = eq(io.decode.csr, UInt<12>(3085))
    node _T_1892 = eq(io.decode.csr, UInt<10>(814))
    node _T_1894 = eq(io.decode.csr, UInt<12>(2830))
    node _T_1896 = eq(io.decode.csr, UInt<12>(3086))
    node _T_1898 = eq(io.decode.csr, UInt<10>(815))
    node _T_1900 = eq(io.decode.csr, UInt<12>(2831))
    node _T_1902 = eq(io.decode.csr, UInt<12>(3087))
    node _T_1904 = eq(io.decode.csr, UInt<10>(816))
    node _T_1906 = eq(io.decode.csr, UInt<12>(2832))
    node _T_1908 = eq(io.decode.csr, UInt<12>(3088))
    node _T_1910 = eq(io.decode.csr, UInt<10>(817))
    node _T_1912 = eq(io.decode.csr, UInt<12>(2833))
    node _T_1914 = eq(io.decode.csr, UInt<12>(3089))
    node _T_1916 = eq(io.decode.csr, UInt<10>(818))
    node _T_1918 = eq(io.decode.csr, UInt<12>(2834))
    node _T_1920 = eq(io.decode.csr, UInt<12>(3090))
    node _T_1922 = eq(io.decode.csr, UInt<10>(819))
    node _T_1924 = eq(io.decode.csr, UInt<12>(2835))
    node _T_1926 = eq(io.decode.csr, UInt<12>(3091))
    node _T_1928 = eq(io.decode.csr, UInt<10>(820))
    node _T_1930 = eq(io.decode.csr, UInt<12>(2836))
    node _T_1932 = eq(io.decode.csr, UInt<12>(3092))
    node _T_1934 = eq(io.decode.csr, UInt<10>(821))
    node _T_1936 = eq(io.decode.csr, UInt<12>(2837))
    node _T_1938 = eq(io.decode.csr, UInt<12>(3093))
    node _T_1940 = eq(io.decode.csr, UInt<10>(822))
    node _T_1942 = eq(io.decode.csr, UInt<12>(2838))
    node _T_1944 = eq(io.decode.csr, UInt<12>(3094))
    node _T_1946 = eq(io.decode.csr, UInt<10>(823))
    node _T_1948 = eq(io.decode.csr, UInt<12>(2839))
    node _T_1950 = eq(io.decode.csr, UInt<12>(3095))
    node _T_1952 = eq(io.decode.csr, UInt<10>(824))
    node _T_1954 = eq(io.decode.csr, UInt<12>(2840))
    node _T_1956 = eq(io.decode.csr, UInt<12>(3096))
    node _T_1958 = eq(io.decode.csr, UInt<10>(825))
    node _T_1960 = eq(io.decode.csr, UInt<12>(2841))
    node _T_1962 = eq(io.decode.csr, UInt<12>(3097))
    node _T_1964 = eq(io.decode.csr, UInt<10>(826))
    node _T_1966 = eq(io.decode.csr, UInt<12>(2842))
    node _T_1968 = eq(io.decode.csr, UInt<12>(3098))
    node _T_1970 = eq(io.decode.csr, UInt<10>(827))
    node _T_1972 = eq(io.decode.csr, UInt<12>(2843))
    node _T_1974 = eq(io.decode.csr, UInt<12>(3099))
    node _T_1976 = eq(io.decode.csr, UInt<10>(828))
    node _T_1978 = eq(io.decode.csr, UInt<12>(2844))
    node _T_1980 = eq(io.decode.csr, UInt<12>(3100))
    node _T_1982 = eq(io.decode.csr, UInt<10>(829))
    node _T_1984 = eq(io.decode.csr, UInt<12>(2845))
    node _T_1986 = eq(io.decode.csr, UInt<12>(3101))
    node _T_1988 = eq(io.decode.csr, UInt<10>(830))
    node _T_1990 = eq(io.decode.csr, UInt<12>(2846))
    node _T_1992 = eq(io.decode.csr, UInt<12>(3102))
    node _T_1994 = eq(io.decode.csr, UInt<10>(831))
    node _T_1996 = eq(io.decode.csr, UInt<12>(2847))
    node _T_1998 = eq(io.decode.csr, UInt<12>(3103))
    node _T_2000 = eq(io.decode.csr, UInt<9>(256))
    node _T_2002 = eq(io.decode.csr, UInt<9>(324))
    node _T_2004 = eq(io.decode.csr, UInt<9>(260))
    node _T_2006 = eq(io.decode.csr, UInt<9>(320))
    node _T_2008 = eq(io.decode.csr, UInt<9>(322))
    node _T_2010 = eq(io.decode.csr, UInt<9>(323))
    node _T_2012 = eq(io.decode.csr, UInt<9>(384))
    node _T_2014 = eq(io.decode.csr, UInt<9>(321))
    node _T_2016 = eq(io.decode.csr, UInt<9>(261))
    node _T_2018 = eq(io.decode.csr, UInt<9>(262))
    node _T_2020 = eq(io.decode.csr, UInt<10>(774))
    node _T_2022 = eq(io.decode.csr, UInt<12>(3072))
    node _T_2024 = eq(io.decode.csr, UInt<12>(3074))
    node _T_2025 = or(_T_1952, _T_1820)
    node _T_2026 = or(_T_2025, _T_1864)
    node _T_2027 = or(_T_2026, _T_2006)
    node _T_2028 = or(_T_2027, _T_1978)
    node _T_2029 = or(_T_2028, _T_1946)
    node _T_2030 = or(_T_2029, _T_1832)
    node _T_2031 = or(_T_2030, _T_1800)
    node _T_2032 = or(_T_2031, _T_2020)
    node _T_2033 = or(_T_2032, _T_1914)
    node _T_2034 = or(_T_2033, _T_1876)
    node _T_2035 = or(_T_2034, _T_1920)
    node _T_2036 = or(_T_2035, _T_1788)
    node _T_2037 = or(_T_2036, _T_1844)
    node _T_2038 = or(_T_2037, _T_1888)
    node _T_2039 = or(_T_2038, _T_1872)
    node _T_2040 = or(_T_2039, _T_1988)
    node _T_2041 = or(_T_2040, _T_1910)
    node _T_2042 = or(_T_2041, _T_1924)
    node _T_2043 = or(_T_2042, _T_1776)
    node _T_2044 = or(_T_2043, _T_1808)
    node _T_2045 = or(_T_2044, _T_1892)
    node _T_2046 = or(_T_2045, _T_1840)
    node _T_2047 = or(_T_2046, _T_1956)
    node _T_2048 = or(_T_2047, _T_2010)
    node _T_2049 = or(_T_2048, _T_1868)
    node _T_2050 = or(_T_2049, _T_2000)
    node _T_2051 = or(_T_2050, _T_1878)
    node _T_2052 = or(_T_2051, _T_1942)
    node _T_2053 = or(_T_2052, _T_1812)
    node _T_2054 = or(_T_2053, _T_1974)
    node _T_2055 = or(_T_2054, _T_1968)
    node _T_2056 = or(_T_2055, _T_1780)
    node _T_2057 = or(_T_2056, _T_1836)
    node _T_2058 = or(_T_2057, _T_1996)
    node _T_2059 = or(_T_2058, _T_1814)
    node _T_2060 = or(_T_2059, _T_1900)
    node _T_2061 = or(_T_2060, _T_1846)
    node _T_2062 = or(_T_2061, _T_1932)
    node _T_2063 = or(_T_2062, _T_1964)
    node _T_2064 = or(_T_2063, _T_1782)
    node _T_2065 = or(_T_2064, _T_1904)
    node _T_2066 = or(_T_2065, _T_1992)
    node _T_2067 = or(_T_2066, _T_1860)
    node _T_2068 = or(_T_2067, _T_1804)
    node _T_2069 = or(_T_2068, _T_1936)
    node _T_2070 = or(_T_2069, _T_1960)
    node _T_2071 = or(_T_2070, _T_1828)
    node _T_2072 = or(_T_2071, _T_1908)
    node _T_2073 = or(_T_2072, _T_2024)
    node _T_2074 = or(_T_2073, _T_2004)
    node _T_2075 = or(_T_2074, _T_1856)
    node _T_2076 = or(_T_2075, _T_1940)
    node _T_2077 = or(_T_2076, _T_1792)
    node _T_2078 = or(_T_2077, _T_1972)
    node _T_2079 = or(_T_2078, _T_1824)
    node _T_2080 = or(_T_2079, _T_1896)
    node _T_2081 = or(_T_2080, _T_1928)
    node _T_2082 = or(_T_2081, _T_1796)
    node _T_2083 = or(_T_2082, _T_1918)
    node _T_2084 = or(_T_2083, _T_1786)
    node _T_2085 = or(_T_2084, _T_1980)
    node _T_2086 = or(_T_2085, _T_1774)
    node _T_2087 = or(_T_2086, _T_1830)
    node _T_2088 = or(_T_2087, _T_1890)
    node _T_2089 = or(_T_2088, _T_2018)
    node _T_2090 = or(_T_2089, _T_1916)
    node _T_2091 = or(_T_2090, _T_1884)
    node _T_2092 = or(_T_2091, _T_1862)
    node _T_2093 = or(_T_2092, _T_1948)
    node _T_2094 = or(_T_2093, _T_1798)
    node _T_2095 = or(_T_2094, _T_1976)
    node _T_2096 = or(_T_2095, _T_1886)
    node _T_2097 = or(_T_2096, _T_1950)
    node _T_2098 = or(_T_2097, _T_1818)
    node _T_2099 = or(_T_2098, _T_1982)
    node _T_2100 = or(_T_2099, _T_1850)
    node _T_2101 = or(_T_2100, _T_1810)
    node _T_2102 = or(_T_2101, _T_1944)
    node _T_2103 = or(_T_2102, _T_2014)
    node _T_2104 = or(_T_2103, _T_1838)
    node _T_2105 = or(_T_2104, _T_1954)
    node _T_2106 = or(_T_2105, _T_1870)
    node _T_2107 = or(_T_2106, _T_1986)
    node _T_2108 = or(_T_2107, _T_2008)
    node _T_2109 = or(_T_2108, _T_1922)
    node _T_2110 = or(_T_2109, _T_1778)
    node _T_2111 = or(_T_2110, _T_1806)
    node _T_2112 = or(_T_2111, _T_1842)
    node _T_2113 = or(_T_2112, _T_1874)
    node _T_2114 = or(_T_2113, _T_1880)
    node _T_2115 = or(_T_2114, _T_2012)
    node _T_2116 = or(_T_2115, _T_1912)
    node _T_2117 = or(_T_2116, _T_1802)
    node _T_2118 = or(_T_2117, _T_1934)
    node _T_2119 = or(_T_2118, _T_1848)
    node _T_2120 = or(_T_2119, _T_1962)
    node _T_2121 = or(_T_2120, _T_1784)
    node _T_2122 = or(_T_2121, _T_1902)
    node _T_2123 = or(_T_2122, _T_1994)
    node _T_2124 = or(_T_2123, _T_2016)
    node _T_2125 = or(_T_2124, _T_1930)
    node _T_2126 = or(_T_2125, _T_1816)
    node _T_2127 = or(_T_2126, _T_1834)
    node _T_2128 = or(_T_2127, _T_1966)
    node _T_2129 = or(_T_2128, _T_1898)
    node _T_2130 = or(_T_2129, _T_1866)
    node _T_2131 = or(_T_2130, _T_1998)
    node _T_2132 = or(_T_2131, _T_1926)
    node _T_2133 = or(_T_2132, _T_1794)
    node _T_2134 = or(_T_2133, _T_1882)
    node _T_2135 = or(_T_2134, _T_1970)
    node _T_2136 = or(_T_2135, _T_1822)
    node _T_2137 = or(_T_2136, _T_1894)
    node _T_2138 = or(_T_2137, _T_2002)
    node _T_2139 = or(_T_2138, _T_1854)
    node _T_2140 = or(_T_2139, _T_1938)
    node _T_2141 = or(_T_2140, _T_1984)
    node _T_2142 = or(_T_2141, _T_1790)
    node _T_2143 = or(_T_2142, _T_1852)
    node _T_2144 = or(_T_2143, _T_1958)
    node _T_2145 = or(_T_2144, _T_1826)
    node _T_2146 = or(_T_2145, _T_2022)
    node _T_2147 = or(_T_2146, _T_1906)
    node _T_2148 = or(_T_2147, _T_1990)
    node _T_2149 = or(_T_2148, _T_1858)
    node _T_2151 = eq(_T_2149, UInt<1>(0))
    node _T_2152 = or(_T_1772, _T_2151)
    node _T_2154 = eq(io.decode.csr, UInt<9>(384))
    node _T_2156 = eq(allow_sfence_vma, UInt<1>(0))
    node _T_2157 = and(_T_2154, _T_2156)
    node _T_2158 = or(_T_2152, _T_2157)
    node _T_2161 = geq(io.decode.csr, UInt<12>(3072))
    node _T_2162 = lt(io.decode.csr, UInt<12>(3104))
    node _T_2163 = and(_T_2161, _T_2162)
    node _T_2166 = geq(io.decode.csr, UInt<12>(3200))
    node _T_2167 = lt(io.decode.csr, UInt<12>(3232))
    node _T_2168 = and(_T_2166, _T_2167)
    node _T_2169 = or(_T_2163, _T_2168)
    node _T_2171 = leq(effective_prv, UInt<1>(1))
    node _T_2172 = and(_T_2169, _T_2171)
    node _T_2173 = bits(io.decode.csr, 11, 0)
    node _T_2174 = dshr(hpm_mask, _T_2173)
    node _T_2175 = bits(_T_2174, 0, 0)
    node _T_2176 = and(_T_2172, _T_2175)
    node _T_2177 = or(_T_2158, _T_2176)
    node _T_2180 = eq(reg_debug, UInt<1>(0))
    node _T_2181 = and(UInt<1>(1), _T_2180)
    node _T_2183 = eq(io.decode.csr, UInt<11>(1968))
    node _T_2185 = eq(io.decode.csr, UInt<11>(1969))
    node _T_2187 = eq(io.decode.csr, UInt<11>(1970))
    node _T_2188 = or(_T_2183, _T_2185)
    node _T_2189 = or(_T_2188, _T_2187)
    node _T_2190 = and(_T_2181, _T_2189)
    node _T_2191 = or(_T_2177, _T_2190)
    node _T_2194 = eq(io.decode.csr, UInt<1>(1))
    node _T_2196 = eq(io.decode.csr, UInt<2>(2))
    node _T_2198 = eq(io.decode.csr, UInt<2>(3))
    node _T_2199 = or(_T_2194, _T_2196)
    node _T_2200 = or(_T_2199, _T_2198)
    node _T_2201 = and(UInt<1>(1), _T_2200)
    node _T_2202 = and(_T_2201, io.decode.fp_illegal)
    node _T_2203 = or(_T_2191, _T_2202)
    io.decode.read_illegal <= _T_2203
    node _T_2204 = bits(io.decode.csr, 11, 10)
    node _T_2205 = not(_T_2204)
    node _T_2207 = eq(_T_2205, UInt<1>(0))
    io.decode.write_illegal <= _T_2207
    node _T_2209 = geq(io.decode.csr, UInt<10>(832))
    node _T_2211 = leq(io.decode.csr, UInt<10>(835))
    node _T_2212 = and(_T_2209, _T_2211)
    node _T_2214 = geq(io.decode.csr, UInt<9>(320))
    node _T_2216 = leq(io.decode.csr, UInt<9>(323))
    node _T_2217 = and(_T_2214, _T_2216)
    node _T_2218 = or(_T_2212, _T_2217)
    node _T_2220 = eq(_T_2218, UInt<1>(0))
    io.decode.write_flush <= _T_2220
    node _T_2221 = bits(io.decode.csr, 9, 8)
    node _T_2222 = lt(effective_prv, _T_2221)
    node _T_2223 = bits(io.decode.csr, 5, 5)
    node _T_2225 = eq(_T_2223, UInt<1>(0))
    node _T_2226 = bits(io.decode.csr, 2, 2)
    node _T_2227 = and(_T_2225, _T_2226)
    node _T_2229 = eq(allow_wfi, UInt<1>(0))
    node _T_2230 = and(_T_2227, _T_2229)
    node _T_2231 = or(_T_2222, _T_2230)
    node _T_2232 = bits(io.decode.csr, 5, 5)
    node _T_2234 = eq(_T_2232, UInt<1>(0))
    node _T_2235 = bits(io.decode.csr, 1, 1)
    node _T_2236 = and(_T_2234, _T_2235)
    node _T_2238 = eq(allow_sret, UInt<1>(0))
    node _T_2239 = and(_T_2236, _T_2238)
    node _T_2240 = or(_T_2231, _T_2239)
    node _T_2241 = bits(io.decode.csr, 5, 5)
    node _T_2243 = eq(allow_sfence_vma, UInt<1>(0))
    node _T_2244 = and(_T_2241, _T_2243)
    node _T_2245 = or(_T_2240, _T_2244)
    io.decode.system_illegal <= _T_2245
    node _T_2247 = add(reg_mstatus.prv, UInt<4>(8))
    node _T_2248 = tail(_T_2247, 1)
    node _T_2250 = mux(insn_break, UInt<2>(3), io.cause)
    node cause = mux(insn_call, _T_2248, _T_2250)
    node cause_lsbs = bits(cause, 5, 0)
    node _T_2251 = bits(cause, 63, 63)
    node _T_2267 = eq(cause_lsbs, UInt<4>(13))
    node causeIsDebugInt = and(_T_2251, _T_2267)
    node _T_2268 = bits(cause, 63, 63)
    node _T_2270 = eq(_T_2268, UInt<1>(0))
    node _T_2300 = eq(cause_lsbs, UInt<4>(13))
    node causeIsDebugTrigger = and(_T_2270, _T_2300)
    node _T_2301 = bits(cause, 63, 63)
    node _T_2303 = eq(_T_2301, UInt<1>(0))
    node _T_2304 = and(_T_2303, insn_break)
    node _T_2305 = cat(reg_dcsr.ebreaks, reg_dcsr.ebreaku)
    node _T_2306 = cat(reg_dcsr.ebreakm, reg_dcsr.ebreakh)
    node _T_2307 = cat(_T_2306, _T_2305)
    node _T_2308 = dshr(_T_2307, reg_mstatus.prv)
    node _T_2309 = bits(_T_2308, 0, 0)
    node causeIsDebugBreak = and(_T_2304, _T_2309)
    node _T_2311 = or(reg_singleStepped, causeIsDebugInt)
    node _T_2312 = or(_T_2311, causeIsDebugTrigger)
    node _T_2313 = or(_T_2312, causeIsDebugBreak)
    node _T_2314 = or(_T_2313, reg_debug)
    node trapToDebug = and(UInt<1>(1), _T_2314)
    node _T_2317 = leq(reg_mstatus.prv, UInt<1>(1))
    node _T_2318 = and(UInt<1>(1), _T_2317)
    node _T_2319 = bits(cause, 63, 63)
    node _T_2320 = dshr(reg_mideleg, cause_lsbs)
    node _T_2321 = bits(_T_2320, 0, 0)
    node _T_2322 = dshr(reg_medeleg, cause_lsbs)
    node _T_2323 = bits(_T_2322, 0, 0)
    node _T_2324 = mux(_T_2319, _T_2321, _T_2323)
    node delegate = and(_T_2318, _T_2324)
    node debugTVec = mux(reg_debug, UInt<12>(2056), UInt<12>(2048))
    node _T_2327 = bits(reg_stvec, 38, 38)
    node _T_2328 = cat(_T_2327, reg_stvec)
    node _T_2329 = mux(delegate, _T_2328, reg_mtvec)
    node tvec = mux(trapToDebug, debugTVec, _T_2329)
    io.fatc <= insn_sfence_vma
    io.evec <= tvec
    io.ptbr <= reg_sptbr
    node _T_2330 = or(insn_call, insn_break)
    node _T_2331 = or(_T_2330, insn_ret)
    io.eret <= _T_2331
    node _T_2333 = eq(reg_debug, UInt<1>(0))
    node _T_2334 = and(reg_dcsr.step, _T_2333)
    io.singleStep <= _T_2334
    io.status <= reg_mstatus
    node _T_2335 = not(io.status.fs)
    node _T_2337 = eq(_T_2335, UInt<1>(0))
    node _T_2338 = not(io.status.xs)
    node _T_2340 = eq(_T_2338, UInt<1>(0))
    node _T_2341 = or(_T_2337, _T_2340)
    io.status.sd <= _T_2341
    io.status.debug <= reg_debug
    io.status.isa <= reg_misa
    io.status.uxl <= UInt<2>(2)
    io.status.sxl <= UInt<2>(2)
    node _T_2344 = or(insn_call, insn_break)
    node exception = or(_T_2344, io.exception)
    node _T_2345 = add(insn_ret, insn_call)
    node _T_2346 = add(insn_break, io.exception)
    node _T_2347 = add(_T_2345, _T_2346)
    node _T_2349 = leq(_T_2347, UInt<1>(1))
    node _T_2350 = or(_T_2349, reset_wky)
    node _T_2352 = eq(_T_2350, UInt<1>(0))
    when _T_2352 : 
{
      skip
}
    when insn_wfi : 
{
      reg_wfi <= UInt<1>(1)
      skip
}
    node _T_2355 = neq(pending_interrupts, UInt<1>(0))
    node _T_2356 = or(_T_2355, exception)
    when _T_2356 : 
{
      reg_wfi <= UInt<1>(0)
      skip
}
    node _T_2359 = eq(reg_wfi, UInt<1>(0))
    node _T_2361 = eq(io.retire, UInt<1>(0))
    node _T_2362 = or(_T_2359, _T_2361)
    node _T_2363 = or(_T_2362, reset_wky)
    node _T_2365 = eq(_T_2363, UInt<1>(0))
    when _T_2365 : 
{
      skip
}
    node _T_2366 = bits(io.retire, 0, 0)
    when _T_2366 : 
{
      reg_singleStepped <= UInt<1>(1)
      skip
}
    node _T_2369 = eq(io.singleStep, UInt<1>(0))
    when _T_2369 : 
{
      reg_singleStepped <= UInt<1>(0)
      skip
}
    node _T_2372 = eq(io.singleStep, UInt<1>(0))
    node _T_2374 = leq(io.retire, UInt<1>(1))
    node _T_2375 = or(_T_2372, _T_2374)
    node _T_2376 = or(_T_2375, reset_wky)
    node _T_2378 = eq(_T_2376, UInt<1>(0))
    when _T_2378 : 
{
      skip
}
    node _T_2380 = eq(reg_singleStepped, UInt<1>(0))
    node _T_2382 = eq(io.retire, UInt<1>(0))
    node _T_2383 = or(_T_2380, _T_2382)
    node _T_2384 = or(_T_2383, reset_wky)
    node _T_2386 = eq(_T_2384, UInt<1>(0))
    when _T_2386 : 
{
      skip
}
    when exception : 
{
      node _T_2387 = not(io.pc)
      node _T_2389 = or(_T_2387, UInt<1>(1))
      node _T_2390 = not(_T_2389)
      node _T_2391 = dshr(read_mstatus, reg_mstatus.prv)
      node _T_2392 = bits(_T_2391, 0, 0)
      node _T_2400 = eq(cause, UInt<2>(3))
      node _T_2401 = eq(cause, UInt<3>(4))
      node _T_2402 = eq(cause, UInt<3>(6))
      node _T_2403 = eq(cause, UInt<1>(0))
      node _T_2404 = eq(cause, UInt<3>(5))
      node _T_2405 = eq(cause, UInt<3>(7))
      node _T_2406 = eq(cause, UInt<1>(1))
      node _T_2407 = or(_T_2400, _T_2401)
      node _T_2408 = or(_T_2407, _T_2402)
      node _T_2409 = or(_T_2408, _T_2403)
      node _T_2410 = or(_T_2409, _T_2404)
      node _T_2411 = or(_T_2410, _T_2405)
      node _T_2412 = or(_T_2411, _T_2406)
      when trapToDebug : 
{
        reg_debug <= UInt<1>(1)
        reg_dpc <= _T_2390
        node _T_2418 = mux(causeIsDebugTrigger, UInt<2>(2), UInt<1>(1))
        node _T_2419 = mux(causeIsDebugInt, UInt<2>(3), _T_2418)
        node _T_2420 = mux(reg_singleStepped, UInt<3>(4), _T_2419)
        reg_dcsr.cause <= _T_2420
        reg_dcsr.prv <= reg_mstatus.prv
        skip
}
      node _T_2422 = eq(trapToDebug, UInt<1>(0))
      node _T_2423 = and(_T_2422, delegate)
      when _T_2423 : 
{
        node _T_2424 = not(_T_2390)
        node _T_2425 = bits(reg_misa, 2, 2)
        node _T_2427 = eq(_T_2425, UInt<1>(0))
        node _T_2429 = cat(_T_2427, UInt<1>(1))
        node _T_2430 = or(_T_2424, _T_2429)
        node _T_2431 = not(_T_2430)
        reg_sepc <= _T_2431
        reg_scause <= cause
        when _T_2412 : 
{
          reg_sbadaddr <= io.badaddr
          skip
}
        reg_mstatus.spie <= _T_2392
        reg_mstatus.spp <= reg_mstatus.prv
        reg_mstatus.sie <= UInt<1>(0)
        new_prv <= UInt<1>(1)
        skip
}
      node _T_2435 = eq(trapToDebug, UInt<1>(0))
      node _T_2437 = eq(delegate, UInt<1>(0))
      node _T_2438 = and(_T_2435, _T_2437)
      when _T_2438 : 
{
        node _T_2439 = not(_T_2390)
        node _T_2440 = bits(reg_misa, 2, 2)
        node _T_2442 = eq(_T_2440, UInt<1>(0))
        node _T_2444 = cat(_T_2442, UInt<1>(1))
        node _T_2445 = or(_T_2439, _T_2444)
        node _T_2446 = not(_T_2445)
        reg_mepc <= _T_2446
        reg_mcause <= cause
        when _T_2412 : 
{
          reg_mbadaddr <= io.badaddr
          skip
}
        reg_mstatus.mpie <= _T_2392
        reg_mstatus.mpp <= reg_mstatus.prv
        reg_mstatus.mie <= UInt<1>(0)
        new_prv <= UInt<2>(3)
        skip
}
      skip
}
    when insn_ret : 
{
      node _T_2450 = bits(io.rw.addr, 9, 9)
      node _T_2452 = eq(_T_2450, UInt<1>(0))
      node _T_2453 = and(UInt<1>(1), _T_2452)
      when _T_2453 : 
{
        node _T_2454 = bits(reg_mstatus.spp, 0, 0)
        when _T_2454 : 
{
          reg_mstatus.sie <= reg_mstatus.spie
          skip
}
        reg_mstatus.spie <= UInt<1>(1)
        reg_mstatus.spp <= UInt<1>(0)
        new_prv <= reg_mstatus.spp
        io.evec <= reg_sepc
        skip
}
      node _T_2458 = bits(io.rw.addr, 10, 10)
      node _T_2459 = and(UInt<1>(1), _T_2458)
      node _T_2461 = eq(_T_2453, UInt<1>(0))
      node _T_2462 = and(_T_2461, _T_2459)
      when _T_2462 : 
{
        new_prv <= reg_dcsr.prv
        reg_debug <= UInt<1>(0)
        io.evec <= reg_dpc
        skip
}
      node _T_2465 = eq(_T_2453, UInt<1>(0))
      node _T_2467 = eq(_T_2459, UInt<1>(0))
      node _T_2468 = and(_T_2465, _T_2467)
      when _T_2468 : 
{
        node _T_2469 = bits(reg_mstatus.mpp, 1, 1)
        when _T_2469 : 
{
          reg_mstatus.mie <= reg_mstatus.mpie
          skip
}
        node _T_2471 = bits(reg_mstatus.mpp, 0, 0)
        node _T_2472 = and(UInt<1>(1), _T_2471)
        node _T_2474 = eq(_T_2469, UInt<1>(0))
        node _T_2475 = and(_T_2474, _T_2472)
        when _T_2475 : 
{
          reg_mstatus.sie <= reg_mstatus.mpie
          skip
}
        reg_mstatus.mpie <= UInt<1>(1)
        node _T_2479 = eq(UInt<1>(0), UInt<2>(2))
        node _T_2481 = mux(_T_2479, UInt<1>(0), UInt<1>(0))
        reg_mstatus.mpp <= _T_2481
        new_prv <= reg_mstatus.mpp
        io.evec <= reg_mepc
        skip
}
      skip
}
    io.time <= _T_950
    io.csr_stall <= reg_wfi
    node _T_2483 = mux(_T_1467, reg_tselect, UInt<1>(0))
    node _T_2485 = mux(_T_1469, _T_1304, UInt<1>(0))
    node _T_2487 = mux(_T_1471, _T_1345, UInt<1>(0))
    node _T_2489 = mux(_T_1473, UInt<1>(0), UInt<1>(0))
    node _T_2491 = mux(_T_1475, UInt<1>(0), UInt<1>(0))
    node _T_2493 = mux(_T_1477, UInt<1>(0), UInt<1>(0))
    node _T_2495 = mux(_T_1479, _T_950, UInt<1>(0))
    node _T_2497 = mux(_T_1481, _T_939, UInt<1>(0))
    node _T_2499 = mux(_T_1483, reg_misa, UInt<1>(0))
    node _T_2501 = mux(_T_1485, read_mstatus, UInt<1>(0))
    node _T_2503 = mux(_T_1487, reg_mtvec, UInt<1>(0))
    node _T_2505 = mux(_T_1489, read_mip, UInt<1>(0))
    node _T_2507 = mux(_T_1491, reg_mie, UInt<1>(0))
    node _T_2509 = mux(_T_1493, reg_mideleg, UInt<1>(0))
    node _T_2511 = mux(_T_1495, reg_medeleg, UInt<1>(0))
    node _T_2513 = mux(_T_1497, reg_mscratch, UInt<1>(0))
    node _T_2515 = mux(_T_1499, _T_1354, UInt<1>(0))
    node _T_2517 = mux(_T_1501, _T_1360, UInt<1>(0))
    node _T_2519 = mux(_T_1503, reg_mcause, UInt<1>(0))
    node _T_2521 = mux(_T_1505, io.hartid, UInt<1>(0))
    node _T_2523 = mux(_T_1507, _T_1376, UInt<1>(0))
    node _T_2525 = mux(_T_1509, reg_dpc, UInt<1>(0))
    node _T_2527 = mux(_T_1511, reg_dscratch, UInt<1>(0))
    node _T_2529 = mux(_T_1513, reg_fflags, UInt<1>(0))
    node _T_2531 = mux(_T_1515, reg_frm, UInt<1>(0))
    node _T_2533 = mux(_T_1517, _T_1377, UInt<1>(0))
    node _T_2535 = mux(_T_1519, UInt<1>(0), UInt<1>(0))
    node _T_2537 = mux(_T_1521, UInt<1>(0), UInt<1>(0))
    node _T_2539 = mux(_T_1523, UInt<1>(0), UInt<1>(0))
    node _T_2541 = mux(_T_1525, UInt<1>(0), UInt<1>(0))
    node _T_2543 = mux(_T_1527, UInt<1>(0), UInt<1>(0))
    node _T_2545 = mux(_T_1529, UInt<1>(0), UInt<1>(0))
    node _T_2547 = mux(_T_1531, UInt<1>(0), UInt<1>(0))
    node _T_2549 = mux(_T_1533, UInt<1>(0), UInt<1>(0))
    node _T_2551 = mux(_T_1535, UInt<1>(0), UInt<1>(0))
    node _T_2553 = mux(_T_1537, UInt<1>(0), UInt<1>(0))
    node _T_2555 = mux(_T_1539, UInt<1>(0), UInt<1>(0))
    node _T_2557 = mux(_T_1541, UInt<1>(0), UInt<1>(0))
    node _T_2559 = mux(_T_1543, UInt<1>(0), UInt<1>(0))
    node _T_2561 = mux(_T_1545, UInt<1>(0), UInt<1>(0))
    node _T_2563 = mux(_T_1547, UInt<1>(0), UInt<1>(0))
    node _T_2565 = mux(_T_1549, UInt<1>(0), UInt<1>(0))
    node _T_2567 = mux(_T_1551, UInt<1>(0), UInt<1>(0))
    node _T_2569 = mux(_T_1553, UInt<1>(0), UInt<1>(0))
    node _T_2571 = mux(_T_1555, UInt<1>(0), UInt<1>(0))
    node _T_2573 = mux(_T_1557, UInt<1>(0), UInt<1>(0))
    node _T_2575 = mux(_T_1559, UInt<1>(0), UInt<1>(0))
    node _T_2577 = mux(_T_1561, UInt<1>(0), UInt<1>(0))
    node _T_2579 = mux(_T_1563, UInt<1>(0), UInt<1>(0))
    node _T_2581 = mux(_T_1565, UInt<1>(0), UInt<1>(0))
    node _T_2583 = mux(_T_1567, UInt<1>(0), UInt<1>(0))
    node _T_2585 = mux(_T_1569, UInt<1>(0), UInt<1>(0))
    node _T_2587 = mux(_T_1571, UInt<1>(0), UInt<1>(0))
    node _T_2589 = mux(_T_1573, UInt<1>(0), UInt<1>(0))
    node _T_2591 = mux(_T_1575, UInt<1>(0), UInt<1>(0))
    node _T_2593 = mux(_T_1577, UInt<1>(0), UInt<1>(0))
    node _T_2595 = mux(_T_1579, UInt<1>(0), UInt<1>(0))
    node _T_2597 = mux(_T_1581, UInt<1>(0), UInt<1>(0))
    node _T_2599 = mux(_T_1583, UInt<1>(0), UInt<1>(0))
    node _T_2601 = mux(_T_1585, UInt<1>(0), UInt<1>(0))
    node _T_2603 = mux(_T_1587, UInt<1>(0), UInt<1>(0))
    node _T_2605 = mux(_T_1589, UInt<1>(0), UInt<1>(0))
    node _T_2607 = mux(_T_1591, UInt<1>(0), UInt<1>(0))
    node _T_2609 = mux(_T_1593, UInt<1>(0), UInt<1>(0))
    node _T_2611 = mux(_T_1595, UInt<1>(0), UInt<1>(0))
    node _T_2613 = mux(_T_1597, UInt<1>(0), UInt<1>(0))
    node _T_2615 = mux(_T_1599, UInt<1>(0), UInt<1>(0))
    node _T_2617 = mux(_T_1601, UInt<1>(0), UInt<1>(0))
    node _T_2619 = mux(_T_1603, UInt<1>(0), UInt<1>(0))
    node _T_2621 = mux(_T_1605, UInt<1>(0), UInt<1>(0))
    node _T_2623 = mux(_T_1607, UInt<1>(0), UInt<1>(0))
    node _T_2625 = mux(_T_1609, UInt<1>(0), UInt<1>(0))
    node _T_2627 = mux(_T_1611, UInt<1>(0), UInt<1>(0))
    node _T_2629 = mux(_T_1613, UInt<1>(0), UInt<1>(0))
    node _T_2631 = mux(_T_1615, UInt<1>(0), UInt<1>(0))
    node _T_2633 = mux(_T_1617, UInt<1>(0), UInt<1>(0))
    node _T_2635 = mux(_T_1619, UInt<1>(0), UInt<1>(0))
    node _T_2637 = mux(_T_1621, UInt<1>(0), UInt<1>(0))
    node _T_2639 = mux(_T_1623, UInt<1>(0), UInt<1>(0))
    node _T_2641 = mux(_T_1625, UInt<1>(0), UInt<1>(0))
    node _T_2643 = mux(_T_1627, UInt<1>(0), UInt<1>(0))
    node _T_2645 = mux(_T_1629, UInt<1>(0), UInt<1>(0))
    node _T_2647 = mux(_T_1631, UInt<1>(0), UInt<1>(0))
    node _T_2649 = mux(_T_1633, UInt<1>(0), UInt<1>(0))
    node _T_2651 = mux(_T_1635, UInt<1>(0), UInt<1>(0))
    node _T_2653 = mux(_T_1637, UInt<1>(0), UInt<1>(0))
    node _T_2655 = mux(_T_1639, UInt<1>(0), UInt<1>(0))
    node _T_2657 = mux(_T_1641, UInt<1>(0), UInt<1>(0))
    node _T_2659 = mux(_T_1643, UInt<1>(0), UInt<1>(0))
    node _T_2661 = mux(_T_1645, UInt<1>(0), UInt<1>(0))
    node _T_2663 = mux(_T_1647, UInt<1>(0), UInt<1>(0))
    node _T_2665 = mux(_T_1649, UInt<1>(0), UInt<1>(0))
    node _T_2667 = mux(_T_1651, UInt<1>(0), UInt<1>(0))
    node _T_2669 = mux(_T_1653, UInt<1>(0), UInt<1>(0))
    node _T_2671 = mux(_T_1655, UInt<1>(0), UInt<1>(0))
    node _T_2673 = mux(_T_1657, UInt<1>(0), UInt<1>(0))
    node _T_2675 = mux(_T_1659, UInt<1>(0), UInt<1>(0))
    node _T_2677 = mux(_T_1661, UInt<1>(0), UInt<1>(0))
    node _T_2679 = mux(_T_1663, UInt<1>(0), UInt<1>(0))
    node _T_2681 = mux(_T_1665, UInt<1>(0), UInt<1>(0))
    node _T_2683 = mux(_T_1667, UInt<1>(0), UInt<1>(0))
    node _T_2685 = mux(_T_1669, UInt<1>(0), UInt<1>(0))
    node _T_2687 = mux(_T_1671, UInt<1>(0), UInt<1>(0))
    node _T_2689 = mux(_T_1673, UInt<1>(0), UInt<1>(0))
    node _T_2691 = mux(_T_1675, UInt<1>(0), UInt<1>(0))
    node _T_2693 = mux(_T_1677, UInt<1>(0), UInt<1>(0))
    node _T_2695 = mux(_T_1679, UInt<1>(0), UInt<1>(0))
    node _T_2697 = mux(_T_1681, UInt<1>(0), UInt<1>(0))
    node _T_2699 = mux(_T_1683, UInt<1>(0), UInt<1>(0))
    node _T_2701 = mux(_T_1685, UInt<1>(0), UInt<1>(0))
    node _T_2703 = mux(_T_1687, UInt<1>(0), UInt<1>(0))
    node _T_2705 = mux(_T_1689, UInt<1>(0), UInt<1>(0))
    node _T_2707 = mux(_T_1691, UInt<1>(0), UInt<1>(0))
    node _T_2709 = mux(_T_1693, _T_1445, UInt<1>(0))
    node _T_2711 = mux(_T_1695, _T_1381, UInt<1>(0))
    node _T_2713 = mux(_T_1697, _T_1380, UInt<1>(0))
    node _T_2715 = mux(_T_1699, reg_sscratch, UInt<1>(0))
    node _T_2717 = mux(_T_1701, reg_scause, UInt<1>(0))
    node _T_2719 = mux(_T_1703, _T_1451, UInt<1>(0))
    node _T_2721 = mux(_T_1705, _T_1453, UInt<1>(0))
    node _T_2723 = mux(_T_1707, _T_1459, UInt<1>(0))
    node _T_2725 = mux(_T_1709, _T_1465, UInt<1>(0))
    node _T_2727 = mux(_T_1711, reg_scounteren, UInt<1>(0))
    node _T_2729 = mux(_T_1713, reg_mcounteren, UInt<1>(0))
    node _T_2731 = mux(_T_1715, _T_950, UInt<1>(0))
    node _T_2733 = mux(_T_1717, _T_939, UInt<1>(0))
    node _T_2735 = or(_T_2483, _T_2485)
    node _T_2736 = or(_T_2735, _T_2487)
    node _T_2737 = or(_T_2736, _T_2489)
    node _T_2738 = or(_T_2737, _T_2491)
    node _T_2739 = or(_T_2738, _T_2493)
    node _T_2740 = or(_T_2739, _T_2495)
    node _T_2741 = or(_T_2740, _T_2497)
    node _T_2742 = or(_T_2741, _T_2499)
    node _T_2743 = or(_T_2742, _T_2501)
    node _T_2744 = or(_T_2743, _T_2503)
    node _T_2745 = or(_T_2744, _T_2505)
    node _T_2746 = or(_T_2745, _T_2507)
    node _T_2747 = or(_T_2746, _T_2509)
    node _T_2748 = or(_T_2747, _T_2511)
    node _T_2749 = or(_T_2748, _T_2513)
    node _T_2750 = or(_T_2749, _T_2515)
    node _T_2751 = or(_T_2750, _T_2517)
    node _T_2752 = or(_T_2751, _T_2519)
    node _T_2753 = or(_T_2752, _T_2521)
    node _T_2754 = or(_T_2753, _T_2523)
    node _T_2755 = or(_T_2754, _T_2525)
    node _T_2756 = or(_T_2755, _T_2527)
    node _T_2757 = or(_T_2756, _T_2529)
    node _T_2758 = or(_T_2757, _T_2531)
    node _T_2759 = or(_T_2758, _T_2533)
    node _T_2760 = or(_T_2759, _T_2535)
    node _T_2761 = or(_T_2760, _T_2537)
    node _T_2762 = or(_T_2761, _T_2539)
    node _T_2763 = or(_T_2762, _T_2541)
    node _T_2764 = or(_T_2763, _T_2543)
    node _T_2765 = or(_T_2764, _T_2545)
    node _T_2766 = or(_T_2765, _T_2547)
    node _T_2767 = or(_T_2766, _T_2549)
    node _T_2768 = or(_T_2767, _T_2551)
    node _T_2769 = or(_T_2768, _T_2553)
    node _T_2770 = or(_T_2769, _T_2555)
    node _T_2771 = or(_T_2770, _T_2557)
    node _T_2772 = or(_T_2771, _T_2559)
    node _T_2773 = or(_T_2772, _T_2561)
    node _T_2774 = or(_T_2773, _T_2563)
    node _T_2775 = or(_T_2774, _T_2565)
    node _T_2776 = or(_T_2775, _T_2567)
    node _T_2777 = or(_T_2776, _T_2569)
    node _T_2778 = or(_T_2777, _T_2571)
    node _T_2779 = or(_T_2778, _T_2573)
    node _T_2780 = or(_T_2779, _T_2575)
    node _T_2781 = or(_T_2780, _T_2577)
    node _T_2782 = or(_T_2781, _T_2579)
    node _T_2783 = or(_T_2782, _T_2581)
    node _T_2784 = or(_T_2783, _T_2583)
    node _T_2785 = or(_T_2784, _T_2585)
    node _T_2786 = or(_T_2785, _T_2587)
    node _T_2787 = or(_T_2786, _T_2589)
    node _T_2788 = or(_T_2787, _T_2591)
    node _T_2789 = or(_T_2788, _T_2593)
    node _T_2790 = or(_T_2789, _T_2595)
    node _T_2791 = or(_T_2790, _T_2597)
    node _T_2792 = or(_T_2791, _T_2599)
    node _T_2793 = or(_T_2792, _T_2601)
    node _T_2794 = or(_T_2793, _T_2603)
    node _T_2795 = or(_T_2794, _T_2605)
    node _T_2796 = or(_T_2795, _T_2607)
    node _T_2797 = or(_T_2796, _T_2609)
    node _T_2798 = or(_T_2797, _T_2611)
    node _T_2799 = or(_T_2798, _T_2613)
    node _T_2800 = or(_T_2799, _T_2615)
    node _T_2801 = or(_T_2800, _T_2617)
    node _T_2802 = or(_T_2801, _T_2619)
    node _T_2803 = or(_T_2802, _T_2621)
    node _T_2804 = or(_T_2803, _T_2623)
    node _T_2805 = or(_T_2804, _T_2625)
    node _T_2806 = or(_T_2805, _T_2627)
    node _T_2807 = or(_T_2806, _T_2629)
    node _T_2808 = or(_T_2807, _T_2631)
    node _T_2809 = or(_T_2808, _T_2633)
    node _T_2810 = or(_T_2809, _T_2635)
    node _T_2811 = or(_T_2810, _T_2637)
    node _T_2812 = or(_T_2811, _T_2639)
    node _T_2813 = or(_T_2812, _T_2641)
    node _T_2814 = or(_T_2813, _T_2643)
    node _T_2815 = or(_T_2814, _T_2645)
    node _T_2816 = or(_T_2815, _T_2647)
    node _T_2817 = or(_T_2816, _T_2649)
    node _T_2818 = or(_T_2817, _T_2651)
    node _T_2819 = or(_T_2818, _T_2653)
    node _T_2820 = or(_T_2819, _T_2655)
    node _T_2821 = or(_T_2820, _T_2657)
    node _T_2822 = or(_T_2821, _T_2659)
    node _T_2823 = or(_T_2822, _T_2661)
    node _T_2824 = or(_T_2823, _T_2663)
    node _T_2825 = or(_T_2824, _T_2665)
    node _T_2826 = or(_T_2825, _T_2667)
    node _T_2827 = or(_T_2826, _T_2669)
    node _T_2828 = or(_T_2827, _T_2671)
    node _T_2829 = or(_T_2828, _T_2673)
    node _T_2830 = or(_T_2829, _T_2675)
    node _T_2831 = or(_T_2830, _T_2677)
    node _T_2832 = or(_T_2831, _T_2679)
    node _T_2833 = or(_T_2832, _T_2681)
    node _T_2834 = or(_T_2833, _T_2683)
    node _T_2835 = or(_T_2834, _T_2685)
    node _T_2836 = or(_T_2835, _T_2687)
    node _T_2837 = or(_T_2836, _T_2689)
    node _T_2838 = or(_T_2837, _T_2691)
    node _T_2839 = or(_T_2838, _T_2693)
    node _T_2840 = or(_T_2839, _T_2695)
    node _T_2841 = or(_T_2840, _T_2697)
    node _T_2842 = or(_T_2841, _T_2699)
    node _T_2843 = or(_T_2842, _T_2701)
    node _T_2844 = or(_T_2843, _T_2703)
    node _T_2845 = or(_T_2844, _T_2705)
    node _T_2846 = or(_T_2845, _T_2707)
    node _T_2847 = or(_T_2846, _T_2709)
    node _T_2848 = or(_T_2847, _T_2711)
    node _T_2849 = or(_T_2848, _T_2713)
    node _T_2850 = or(_T_2849, _T_2715)
    node _T_2851 = or(_T_2850, _T_2717)
    node _T_2852 = or(_T_2851, _T_2719)
    node _T_2853 = or(_T_2852, _T_2721)
    node _T_2854 = or(_T_2853, _T_2723)
    node _T_2855 = or(_T_2854, _T_2725)
    node _T_2856 = or(_T_2855, _T_2727)
    node _T_2857 = or(_T_2856, _T_2729)
    node _T_2858 = or(_T_2857, _T_2731)
    node _T_2859 = or(_T_2858, _T_2733)
    wire _T_2861 : UInt<64>
    _T_2861 is invalid
    _T_2861 <= _T_2859
    io.rw.rdata <= _T_2861
    io.fcsr_rm <= reg_frm
    when io.fcsr_flags.valid : 
{
      node _T_2862 = or(reg_fflags, io.fcsr_flags.bits_wky)
      reg_fflags <= _T_2862
      skip
}
    node _T_2866 = eq(io.rw.cmd, UInt<3>(2))
    node _T_2867 = eq(io.rw.cmd, UInt<3>(3))
    node _T_2868 = eq(io.rw.cmd, UInt<3>(1))
    node _T_2869 = or(_T_2866, _T_2867)
    node _T_2870 = or(_T_2869, _T_2868)
    when _T_2870 : 
{
      when _T_1485 : 
{
        wire _T_2929 : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}
        _T_2929 is invalid
        wire _T_2959 : UInt<99>
        _T_2959 is invalid
        _T_2959 <= wdata
        node _T_2960 = bits(_T_2959, 0, 0)
        _T_2929.uie <= _T_2960
        node _T_2961 = bits(_T_2959, 1, 1)
        _T_2929.sie <= _T_2961
        node _T_2962 = bits(_T_2959, 2, 2)
        _T_2929.hie <= _T_2962
        node _T_2963 = bits(_T_2959, 3, 3)
        _T_2929.mie <= _T_2963
        node _T_2964 = bits(_T_2959, 4, 4)
        _T_2929.upie <= _T_2964
        node _T_2965 = bits(_T_2959, 5, 5)
        _T_2929.spie <= _T_2965
        node _T_2966 = bits(_T_2959, 6, 6)
        _T_2929.hpie <= _T_2966
        node _T_2967 = bits(_T_2959, 7, 7)
        _T_2929.mpie <= _T_2967
        node _T_2968 = bits(_T_2959, 8, 8)
        _T_2929.spp <= _T_2968
        node _T_2969 = bits(_T_2959, 10, 9)
        _T_2929.hpp <= _T_2969
        node _T_2970 = bits(_T_2959, 12, 11)
        _T_2929.mpp <= _T_2970
        node _T_2971 = bits(_T_2959, 14, 13)
        _T_2929.fs <= _T_2971
        node _T_2972 = bits(_T_2959, 16, 15)
        _T_2929.xs <= _T_2972
        node _T_2973 = bits(_T_2959, 17, 17)
        _T_2929.mprv <= _T_2973
        node _T_2974 = bits(_T_2959, 18, 18)
        _T_2929.pum <= _T_2974
        node _T_2975 = bits(_T_2959, 19, 19)
        _T_2929.mxr <= _T_2975
        node _T_2976 = bits(_T_2959, 20, 20)
        _T_2929.tvm <= _T_2976
        node _T_2977 = bits(_T_2959, 21, 21)
        _T_2929.tw <= _T_2977
        node _T_2978 = bits(_T_2959, 22, 22)
        _T_2929.tsr <= _T_2978
        node _T_2979 = bits(_T_2959, 30, 23)
        _T_2929.zero1 <= _T_2979
        node _T_2980 = bits(_T_2959, 31, 31)
        _T_2929.sd_rv32 <= _T_2980
        node _T_2981 = bits(_T_2959, 33, 32)
        _T_2929.uxl <= _T_2981
        node _T_2982 = bits(_T_2959, 35, 34)
        _T_2929.sxl <= _T_2982
        node _T_2983 = bits(_T_2959, 62, 36)
        _T_2929.zero2 <= _T_2983
        node _T_2984 = bits(_T_2959, 63, 63)
        _T_2929.sd <= _T_2984
        node _T_2985 = bits(_T_2959, 65, 64)
        _T_2929.prv <= _T_2985
        node _T_2986 = bits(_T_2959, 97, 66)
        _T_2929.isa <= _T_2986
        node _T_2987 = bits(_T_2959, 98, 98)
        _T_2929.debug <= _T_2987
        reg_mstatus.mie <= _T_2929.mie
        reg_mstatus.mpie <= _T_2929.mpie
        reg_mstatus.mprv <= _T_2929.mprv
        reg_mstatus.mpp <= _T_2929.mpp
        reg_mstatus.mxr <= _T_2929.mxr
        reg_mstatus.pum <= _T_2929.pum
        reg_mstatus.spp <= _T_2929.spp
        reg_mstatus.spie <= _T_2929.spie
        reg_mstatus.sie <= _T_2929.sie
        reg_mstatus.tw <= _T_2929.tw
        reg_mstatus.tvm <= _T_2929.tvm
        reg_mstatus.tsr <= _T_2929.tsr
        node _T_2989 = neq(_T_2929.fs, UInt<1>(0))
        node _T_2990 = bits(_T_2989, 0, 0)
        node _T_2993 = mux(_T_2990, UInt<2>(3), UInt<2>(0))
        reg_mstatus.fs <= _T_2993
        skip
}
      when _T_1483 : 
{
        node _T_2995 = bits(wdata, 5, 5)
        node _T_2996 = not(wdata)
        node _T_2998 = eq(_T_2995, UInt<1>(0))
        node _T_2999 = shl(_T_2998, 3)
        node _T_3000 = or(_T_2996, _T_2999)
        node _T_3001 = not(_T_3000)
        node _T_3002 = and(_T_3001, UInt<13>(4141))
        node _T_3003 = not(UInt<13>(4141))
        node _T_3004 = and(reg_misa, _T_3003)
        node _T_3005 = or(_T_3002, _T_3004)
        reg_misa <= _T_3005
        skip
}
      when _T_1489 : 
{
        wire _T_3034 : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
        _T_3034 is invalid
        wire _T_3049 : UInt<13>
        _T_3049 is invalid
        _T_3049 <= wdata
        node _T_3050 = bits(_T_3049, 0, 0)
        _T_3034.usip <= _T_3050
        node _T_3051 = bits(_T_3049, 1, 1)
        _T_3034.ssip <= _T_3051
        node _T_3052 = bits(_T_3049, 2, 2)
        _T_3034.hsip <= _T_3052
        node _T_3053 = bits(_T_3049, 3, 3)
        _T_3034.msip <= _T_3053
        node _T_3054 = bits(_T_3049, 4, 4)
        _T_3034.utip <= _T_3054
        node _T_3055 = bits(_T_3049, 5, 5)
        _T_3034.stip <= _T_3055
        node _T_3056 = bits(_T_3049, 6, 6)
        _T_3034.htip <= _T_3056
        node _T_3057 = bits(_T_3049, 7, 7)
        _T_3034.mtip <= _T_3057
        node _T_3058 = bits(_T_3049, 8, 8)
        _T_3034.ueip <= _T_3058
        node _T_3059 = bits(_T_3049, 9, 9)
        _T_3034.seip <= _T_3059
        node _T_3060 = bits(_T_3049, 10, 10)
        _T_3034.heip <= _T_3060
        node _T_3061 = bits(_T_3049, 11, 11)
        _T_3034.meip <= _T_3061
        node _T_3062 = bits(_T_3049, 12, 12)
        _T_3034.rocc <= _T_3062
        reg_mip.ssip <= _T_3034.ssip
        reg_mip.stip <= _T_3034.stip
        skip
}
      when _T_1491 : 
{
        node _T_3063 = and(wdata, supported_interrupts)
        reg_mie <= _T_3063
        skip
}
      when _T_1499 : 
{
        node _T_3064 = not(wdata)
        node _T_3065 = bits(reg_misa, 2, 2)
        node _T_3067 = eq(_T_3065, UInt<1>(0))
        node _T_3069 = cat(_T_3067, UInt<1>(1))
        node _T_3070 = or(_T_3064, _T_3069)
        node _T_3071 = not(_T_3070)
        reg_mepc <= _T_3071
        skip
}
      when _T_1497 : 
{
        reg_mscratch <= wdata
        skip
}
      when _T_1487 : 
{
        node _T_3072 = shr(wdata, 2)
        node _T_3073 = shl(_T_3072, 2)
        reg_mtvec <= _T_3073
        skip
}
      when _T_1503 : 
{
        node _T_3075 = and(wdata, UInt<64>(9223372036854775839))
        reg_mcause <= _T_3075
        skip
}
      when _T_1501 : 
{
        node _T_3076 = bits(wdata, 39, 0)
        reg_mbadaddr <= _T_3076
        skip
}
      when _T_1479 : 
{
        node _T_3077 = bits(wdata, 63, 0)
        _T_942 <= _T_3077
        node _T_3078 = shr(_T_3077, 6)
        _T_945 <= _T_3078
        skip
}
      when _T_1481 : 
{
        node _T_3079 = bits(wdata, 63, 0)
        _T_931 <= _T_3079
        node _T_3080 = shr(_T_3079, 6)
        _T_934 <= _T_3080
        skip
}
      when _T_1513 : 
{
        reg_fflags <= wdata
        skip
}
      when _T_1515 : 
{
        reg_frm <= wdata
        skip
}
      when _T_1517 : 
{
        reg_fflags <= wdata
        node _T_3081 = shr(wdata, 5)
        reg_frm <= _T_3081
        skip
}
      when _T_1507 : 
{
        wire _T_3118 : {xdebugver : UInt<2>, ndreset : UInt<1>, fullreset : UInt<1>, zero3 : UInt<12>, ebreakm : UInt<1>, ebreakh : UInt<1>, ebreaks : UInt<1>, ebreaku : UInt<1>, zero2 : UInt<1>, stopcycle : UInt<1>, stoptime : UInt<1>, cause : UInt<3>, debugint : UInt<1>, zero1 : UInt<1>, halt : UInt<1>, step : UInt<1>, prv : UInt<2>}
        _T_3118 is invalid
        wire _T_3137 : UInt<32>
        _T_3137 is invalid
        _T_3137 <= wdata
        node _T_3138 = bits(_T_3137, 1, 0)
        _T_3118.prv <= _T_3138
        node _T_3139 = bits(_T_3137, 2, 2)
        _T_3118.step <= _T_3139
        node _T_3140 = bits(_T_3137, 3, 3)
        _T_3118.halt <= _T_3140
        node _T_3141 = bits(_T_3137, 4, 4)
        _T_3118.zero1 <= _T_3141
        node _T_3142 = bits(_T_3137, 5, 5)
        _T_3118.debugint <= _T_3142
        node _T_3143 = bits(_T_3137, 8, 6)
        _T_3118.cause <= _T_3143
        node _T_3144 = bits(_T_3137, 9, 9)
        _T_3118.stoptime <= _T_3144
        node _T_3145 = bits(_T_3137, 10, 10)
        _T_3118.stopcycle <= _T_3145
        node _T_3146 = bits(_T_3137, 11, 11)
        _T_3118.zero2 <= _T_3146
        node _T_3147 = bits(_T_3137, 12, 12)
        _T_3118.ebreaku <= _T_3147
        node _T_3148 = bits(_T_3137, 13, 13)
        _T_3118.ebreaks <= _T_3148
        node _T_3149 = bits(_T_3137, 14, 14)
        _T_3118.ebreakh <= _T_3149
        node _T_3150 = bits(_T_3137, 15, 15)
        _T_3118.ebreakm <= _T_3150
        node _T_3151 = bits(_T_3137, 27, 16)
        _T_3118.zero3 <= _T_3151
        node _T_3152 = bits(_T_3137, 28, 28)
        _T_3118.fullreset <= _T_3152
        node _T_3153 = bits(_T_3137, 29, 29)
        _T_3118.ndreset <= _T_3153
        node _T_3154 = bits(_T_3137, 31, 30)
        _T_3118.xdebugver <= _T_3154
        reg_dcsr.halt <= _T_3118.halt
        reg_dcsr.step <= _T_3118.step
        reg_dcsr.ebreakm <= _T_3118.ebreakm
        reg_dcsr.ebreaks <= _T_3118.ebreaks
        reg_dcsr.ebreaku <= _T_3118.ebreaku
        reg_dcsr.prv <= _T_3118.prv
        skip
}
      when _T_1509 : 
{
        node _T_3155 = not(wdata)
        node _T_3157 = or(_T_3155, UInt<1>(1))
        node _T_3158 = not(_T_3157)
        reg_dpc <= _T_3158
        skip
}
      when _T_1511 : 
{
        reg_dscratch <= wdata
        skip
}
      when _T_1693 : 
{
        wire _T_3217 : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>}
        _T_3217 is invalid
        wire _T_3247 : UInt<99>
        _T_3247 is invalid
        _T_3247 <= wdata
        node _T_3248 = bits(_T_3247, 0, 0)
        _T_3217.uie <= _T_3248
        node _T_3249 = bits(_T_3247, 1, 1)
        _T_3217.sie <= _T_3249
        node _T_3250 = bits(_T_3247, 2, 2)
        _T_3217.hie <= _T_3250
        node _T_3251 = bits(_T_3247, 3, 3)
        _T_3217.mie <= _T_3251
        node _T_3252 = bits(_T_3247, 4, 4)
        _T_3217.upie <= _T_3252
        node _T_3253 = bits(_T_3247, 5, 5)
        _T_3217.spie <= _T_3253
        node _T_3254 = bits(_T_3247, 6, 6)
        _T_3217.hpie <= _T_3254
        node _T_3255 = bits(_T_3247, 7, 7)
        _T_3217.mpie <= _T_3255
        node _T_3256 = bits(_T_3247, 8, 8)
        _T_3217.spp <= _T_3256
        node _T_3257 = bits(_T_3247, 10, 9)
        _T_3217.hpp <= _T_3257
        node _T_3258 = bits(_T_3247, 12, 11)
        _T_3217.mpp <= _T_3258
        node _T_3259 = bits(_T_3247, 14, 13)
        _T_3217.fs <= _T_3259
        node _T_3260 = bits(_T_3247, 16, 15)
        _T_3217.xs <= _T_3260
        node _T_3261 = bits(_T_3247, 17, 17)
        _T_3217.mprv <= _T_3261
        node _T_3262 = bits(_T_3247, 18, 18)
        _T_3217.pum <= _T_3262
        node _T_3263 = bits(_T_3247, 19, 19)
        _T_3217.mxr <= _T_3263
        node _T_3264 = bits(_T_3247, 20, 20)
        _T_3217.tvm <= _T_3264
        node _T_3265 = bits(_T_3247, 21, 21)
        _T_3217.tw <= _T_3265
        node _T_3266 = bits(_T_3247, 22, 22)
        _T_3217.tsr <= _T_3266
        node _T_3267 = bits(_T_3247, 30, 23)
        _T_3217.zero1 <= _T_3267
        node _T_3268 = bits(_T_3247, 31, 31)
        _T_3217.sd_rv32 <= _T_3268
        node _T_3269 = bits(_T_3247, 33, 32)
        _T_3217.uxl <= _T_3269
        node _T_3270 = bits(_T_3247, 35, 34)
        _T_3217.sxl <= _T_3270
        node _T_3271 = bits(_T_3247, 62, 36)
        _T_3217.zero2 <= _T_3271
        node _T_3272 = bits(_T_3247, 63, 63)
        _T_3217.sd <= _T_3272
        node _T_3273 = bits(_T_3247, 65, 64)
        _T_3217.prv <= _T_3273
        node _T_3274 = bits(_T_3247, 97, 66)
        _T_3217.isa <= _T_3274
        node _T_3275 = bits(_T_3247, 98, 98)
        _T_3217.debug <= _T_3275
        reg_mstatus.sie <= _T_3217.sie
        reg_mstatus.spie <= _T_3217.spie
        reg_mstatus.spp <= _T_3217.spp
        reg_mstatus.pum <= _T_3217.pum
        node _T_3277 = neq(_T_3217.fs, UInt<1>(0))
        node _T_3278 = bits(_T_3277, 0, 0)
        node _T_3281 = mux(_T_3278, UInt<2>(3), UInt<2>(0))
        reg_mstatus.fs <= _T_3281
        skip
}
      when _T_1695 : 
{
        wire _T_3310 : {rocc : UInt<1>, meip : UInt<1>, heip : UInt<1>, seip : UInt<1>, ueip : UInt<1>, mtip : UInt<1>, htip : UInt<1>, stip : UInt<1>, utip : UInt<1>, msip : UInt<1>, hsip : UInt<1>, ssip : UInt<1>, usip : UInt<1>}
        _T_3310 is invalid
        wire _T_3325 : UInt<13>
        _T_3325 is invalid
        _T_3325 <= wdata
        node _T_3326 = bits(_T_3325, 0, 0)
        _T_3310.usip <= _T_3326
        node _T_3327 = bits(_T_3325, 1, 1)
        _T_3310.ssip <= _T_3327
        node _T_3328 = bits(_T_3325, 2, 2)
        _T_3310.hsip <= _T_3328
        node _T_3329 = bits(_T_3325, 3, 3)
        _T_3310.msip <= _T_3329
        node _T_3330 = bits(_T_3325, 4, 4)
        _T_3310.utip <= _T_3330
        node _T_3331 = bits(_T_3325, 5, 5)
        _T_3310.stip <= _T_3331
        node _T_3332 = bits(_T_3325, 6, 6)
        _T_3310.htip <= _T_3332
        node _T_3333 = bits(_T_3325, 7, 7)
        _T_3310.mtip <= _T_3333
        node _T_3334 = bits(_T_3325, 8, 8)
        _T_3310.ueip <= _T_3334
        node _T_3335 = bits(_T_3325, 9, 9)
        _T_3310.seip <= _T_3335
        node _T_3336 = bits(_T_3325, 10, 10)
        _T_3310.heip <= _T_3336
        node _T_3337 = bits(_T_3325, 11, 11)
        _T_3310.meip <= _T_3337
        node _T_3338 = bits(_T_3325, 12, 12)
        _T_3310.rocc <= _T_3338
        reg_mip.ssip <= _T_3310.ssip
        skip
}
      when _T_1705 : 
{
        wire _T_3347 : {mode : UInt<4>, asid : UInt<16>, ppn : UInt<44>}
        _T_3347 is invalid
        wire _T_3352 : UInt<64>
        _T_3352 is invalid
        _T_3352 <= wdata
        node _T_3353 = bits(_T_3352, 43, 0)
        _T_3347.ppn <= _T_3353
        node _T_3354 = bits(_T_3352, 59, 44)
        _T_3347.asid <= _T_3354
        node _T_3355 = bits(_T_3352, 63, 60)
        _T_3347.mode <= _T_3355
        node _T_3357 = eq(_T_3347.mode, UInt<1>(0))
        when _T_3357 : 
{
          reg_sptbr.mode <= UInt<1>(0)
          skip
}
        node _T_3360 = eq(_T_3347.mode, UInt<4>(8))
        when _T_3360 : 
{
          reg_sptbr.mode <= UInt<4>(8)
          skip
}
        node _T_3363 = eq(_T_3347.mode, UInt<1>(0))
        node _T_3365 = eq(_T_3347.mode, UInt<4>(8))
        node _T_3366 = or(_T_3363, _T_3365)
        when _T_3366 : 
{
          node _T_3367 = bits(_T_3347.ppn, 19, 0)
          reg_sptbr.ppn <= _T_3367
          skip
}
        skip
}
      when _T_1697 : 
{
        node _T_3368 = not(reg_mideleg)
        node _T_3369 = and(reg_mie, _T_3368)
        node _T_3370 = and(wdata, reg_mideleg)
        node _T_3371 = or(_T_3369, _T_3370)
        reg_mie <= _T_3371
        skip
}
      when _T_1699 : 
{
        reg_sscratch <= wdata
        skip
}
      when _T_1707 : 
{
        node _T_3372 = not(wdata)
        node _T_3373 = bits(reg_misa, 2, 2)
        node _T_3375 = eq(_T_3373, UInt<1>(0))
        node _T_3377 = cat(_T_3375, UInt<1>(1))
        node _T_3378 = or(_T_3372, _T_3377)
        node _T_3379 = not(_T_3378)
        reg_sepc <= _T_3379
        skip
}
      when _T_1709 : 
{
        node _T_3380 = shr(wdata, 2)
        node _T_3381 = shl(_T_3380, 2)
        reg_stvec <= _T_3381
        skip
}
      when _T_1701 : 
{
        node _T_3383 = and(wdata, UInt<64>(9223372036854775839))
        reg_scause <= _T_3383
        skip
}
      when _T_1703 : 
{
        node _T_3384 = bits(wdata, 39, 0)
        reg_sbadaddr <= _T_3384
        skip
}
      when _T_1493 : 
{
        node _T_3385 = and(wdata, delegable_interrupts)
        reg_mideleg <= _T_3385
        skip
}
      when _T_1495 : 
{
        node _T_3386 = and(wdata, UInt<9>(427))
        reg_medeleg <= _T_3386
        skip
}
      when _T_1711 : 
{
        node _T_3388 = and(wdata, UInt<3>(7))
        reg_scounteren <= _T_3388
        skip
}
      when _T_1713 : 
{
        node _T_3390 = and(wdata, UInt<3>(7))
        reg_mcounteren <= _T_3390
        skip
}
      when _T_1467 : 
{
        reg_tselect <= wdata
        skip
}
      node _T_3427 = eq(reg_bp[reg_tselect].control.dmode, UInt<1>(0))
      node _T_3428 = or(_T_3427, reg_debug)
      when _T_3428 : 
{
        when _T_1469 : 
{
          wire _T_3461 : {ttype : UInt<4>, dmode : UInt<1>, maskmax : UInt<6>, reserved : UInt<40>, action : UInt<1>, chain : UInt<1>, zero : UInt<2>, tmatch : UInt<2>, m : UInt<1>, h : UInt<1>, s : UInt<1>, u : UInt<1>, x : UInt<1>, w : UInt<1>, r : UInt<1>}
          _T_3461 is invalid
          wire _T_3478 : UInt<64>
          _T_3478 is invalid
          _T_3478 <= wdata
          node _T_3479 = bits(_T_3478, 0, 0)
          _T_3461.r <= _T_3479
          node _T_3480 = bits(_T_3478, 1, 1)
          _T_3461.w <= _T_3480
          node _T_3481 = bits(_T_3478, 2, 2)
          _T_3461.x <= _T_3481
          node _T_3482 = bits(_T_3478, 3, 3)
          _T_3461.u <= _T_3482
          node _T_3483 = bits(_T_3478, 4, 4)
          _T_3461.s <= _T_3483
          node _T_3484 = bits(_T_3478, 5, 5)
          _T_3461.h <= _T_3484
          node _T_3485 = bits(_T_3478, 6, 6)
          _T_3461.m <= _T_3485
          node _T_3486 = bits(_T_3478, 8, 7)
          _T_3461.tmatch <= _T_3486
          node _T_3487 = bits(_T_3478, 10, 9)
          _T_3461.zero <= _T_3487
          node _T_3488 = bits(_T_3478, 11, 11)
          _T_3461.chain <= _T_3488
          node _T_3489 = bits(_T_3478, 12, 12)
          _T_3461.action <= _T_3489
          node _T_3490 = bits(_T_3478, 52, 13)
          _T_3461.reserved <= _T_3490
          node _T_3491 = bits(_T_3478, 58, 53)
          _T_3461.maskmax <= _T_3491
          node _T_3492 = bits(_T_3478, 59, 59)
          _T_3461.dmode <= _T_3492
          node _T_3493 = bits(_T_3478, 63, 60)
          _T_3461.ttype <= _T_3493
          node _T_3494 = and(_T_3461.dmode, reg_debug)
          reg_bp[reg_tselect].control <= _T_3461
          reg_bp[reg_tselect].control.dmode <= _T_3494
          node _T_3495 = and(_T_3494, _T_3461.action)
          reg_bp[reg_tselect].control.action <= _T_3495
          skip
}
        when _T_1471 : 
{
          reg_bp[reg_tselect].address <= wdata
          skip
}
        skip
}
      skip
}
    reg_mip <= io.interrupts
    reg_dcsr.debugint <= io.interrupts.debug
    reg_sptbr.asid <= UInt<1>(0)
    reg_tselect <= UInt<1>(0)
    reg_bp[0].control.chain <= UInt<1>(0)
    reg_bp[0].control.ttype <= UInt<2>(2)
    reg_bp[0].control.maskmax <= UInt<3>(4)
    reg_bp[0].control.reserved <= UInt<1>(0)
    reg_bp[0].control.zero <= UInt<1>(0)
    reg_bp[0].control.h <= UInt<1>(0)
    when reset_wky : 
{
      reg_bp[0].control.action <= UInt<1>(0)
      reg_bp[0].control.dmode <= UInt<1>(0)
      reg_bp[0].control.r <= UInt<1>(0)
      reg_bp[0].control.w <= UInt<1>(0)
      reg_bp[0].control.x <= UInt<1>(0)
      skip
}
    reg_bp[1].control.ttype <= UInt<2>(2)
    reg_bp[1].control.maskmax <= UInt<3>(4)
    reg_bp[1].control.reserved <= UInt<1>(0)
    reg_bp[1].control.zero <= UInt<1>(0)
    reg_bp[1].control.h <= UInt<1>(0)
    when reset_wky : 
{
      reg_bp[1].control.action <= UInt<1>(0)
      reg_bp[1].control.dmode <= UInt<1>(0)
      reg_bp[1].control.r <= UInt<1>(0)
      reg_bp[1].control.w <= UInt<1>(0)
      reg_bp[1].control.x <= UInt<1>(0)
      skip
}
    wire _T_3556 : {control : {ttype : UInt<4>, dmode : UInt<1>, maskmax : UInt<6>, reserved : UInt<40>, action : UInt<1>, chain : UInt<1>, zero : UInt<2>, tmatch : UInt<2>, m : UInt<1>, h : UInt<1>, s : UInt<1>, u : UInt<1>, x : UInt<1>, w : UInt<1>, r : UInt<1>}, address : UInt<39>}
    _T_3556 is invalid
    wire _T_3575 : UInt<103>
    _T_3575 is invalid
    _T_3575 <= UInt<1>(0)
    node _T_3576 = bits(_T_3575, 38, 0)
    _T_3556.address <= _T_3576
    node _T_3577 = bits(_T_3575, 102, 39)
    wire _T_3579 : UInt<64>
    _T_3579 is invalid
    _T_3579 <= _T_3577
    node _T_3580 = bits(_T_3579, 0, 0)
    _T_3556.control.r <= _T_3580
    node _T_3581 = bits(_T_3579, 1, 1)
    _T_3556.control.w <= _T_3581
    node _T_3582 = bits(_T_3579, 2, 2)
    _T_3556.control.x <= _T_3582
    node _T_3583 = bits(_T_3579, 3, 3)
    _T_3556.control.u <= _T_3583
    node _T_3584 = bits(_T_3579, 4, 4)
    _T_3556.control.s <= _T_3584
    node _T_3585 = bits(_T_3579, 5, 5)
    _T_3556.control.h <= _T_3585
    node _T_3586 = bits(_T_3579, 6, 6)
    _T_3556.control.m <= _T_3586
    node _T_3587 = bits(_T_3579, 8, 7)
    _T_3556.control.tmatch <= _T_3587
    node _T_3588 = bits(_T_3579, 10, 9)
    _T_3556.control.zero <= _T_3588
    node _T_3589 = bits(_T_3579, 11, 11)
    _T_3556.control.chain <= _T_3589
    node _T_3590 = bits(_T_3579, 12, 12)
    _T_3556.control.action <= _T_3590
    node _T_3591 = bits(_T_3579, 52, 13)
    _T_3556.control.reserved <= _T_3591
    node _T_3592 = bits(_T_3579, 58, 53)
    _T_3556.control.maskmax <= _T_3592
    node _T_3593 = bits(_T_3579, 59, 59)
    _T_3556.control.dmode <= _T_3593
    node _T_3594 = bits(_T_3579, 63, 60)
    _T_3556.control.ttype <= _T_3594
    reg_bp[1] <= _T_3556
  module BreakpointUnit : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip status : {debug : UInt<1>, isa : UInt<32>, prv : UInt<2>, sd : UInt<1>, zero2 : UInt<27>, sxl : UInt<2>, uxl : UInt<2>, sd_rv32 : UInt<1>, zero1 : UInt<8>, tsr : UInt<1>, tw : UInt<1>, tvm : UInt<1>, mxr : UInt<1>, pum : UInt<1>, mprv : UInt<1>, xs : UInt<2>, fs : UInt<2>, mpp : UInt<2>, hpp : UInt<2>, spp : UInt<1>, mpie : UInt<1>, hpie : UInt<1>, spie : UInt<1>, upie : UInt<1>, mie : UInt<1>, hie : UInt<1>, sie : UInt<1>, uie : UInt<1>},  flip bp : {control : {ttype : UInt<4>, dmode : UInt<1>, maskmax : UInt<6>, reserved : UInt<40>, action : UInt<1>, chain : UInt<1>, zero : UInt<2>, tmatch : UInt<2>, m : UInt<1>, h : UInt<1>, s : UInt<1>, u : UInt<1>, x : UInt<1>, w : UInt<1>, r : UInt<1>}, address : UInt<39>}[1],  flip pc : UInt<39>,  flip ea : UInt<39>, xcpt_if : UInt<1>, xcpt_ld : UInt<1>, xcpt_st : UInt<1>, debug_if : UInt<1>, debug_ld : UInt<1>, debug_st : UInt<1>}
    io is invalid
    io is invalid
    io.xcpt_if <= UInt<1>(0)
    io.xcpt_ld <= UInt<1>(0)
    io.xcpt_st <= UInt<1>(0)
    io.debug_if <= UInt<1>(0)
    io.debug_ld <= UInt<1>(0)
    io.debug_st <= UInt<1>(0)
    node _T_212 = eq(io.status.debug, UInt<1>(0))
    node _T_213 = cat(io.bp[0].control.s, io.bp[0].control.u)
    node _T_214 = cat(io.bp[0].control.m, io.bp[0].control.h)
    node _T_215 = cat(_T_214, _T_213)
    node _T_216 = dshr(_T_215, io.status.prv)
    node _T_217 = bits(_T_216, 0, 0)
    node _T_218 = and(_T_212, _T_217)
    node _T_219 = and(_T_218, UInt<1>(1))
    node _T_220 = and(_T_219, io.bp[0].control.r)
    node _T_221 = bits(io.bp[0].control.tmatch, 1, 1)
    node _T_222 = geq(io.ea, io.bp[0].address)
    node _T_223 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_224 = xor(_T_222, _T_223)
    node _T_225 = not(io.ea)
    node _T_226 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_227 = bits(io.bp[0].address, 0, 0)
    node _T_228 = and(_T_226, _T_227)
    node _T_229 = bits(io.bp[0].address, 1, 1)
    node _T_230 = and(_T_228, _T_229)
    node _T_231 = bits(io.bp[0].address, 2, 2)
    node _T_232 = and(_T_230, _T_231)
    node _T_233 = cat(_T_228, _T_226)
    node _T_234 = cat(_T_232, _T_230)
    node _T_235 = cat(_T_234, _T_233)
    node _T_236 = or(_T_225, _T_235)
    node _T_237 = not(io.bp[0].address)
    node _T_238 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_239 = bits(io.bp[0].address, 0, 0)
    node _T_240 = and(_T_238, _T_239)
    node _T_241 = bits(io.bp[0].address, 1, 1)
    node _T_242 = and(_T_240, _T_241)
    node _T_243 = bits(io.bp[0].address, 2, 2)
    node _T_244 = and(_T_242, _T_243)
    node _T_245 = cat(_T_240, _T_238)
    node _T_246 = cat(_T_244, _T_242)
    node _T_247 = cat(_T_246, _T_245)
    node _T_248 = or(_T_237, _T_247)
    node _T_249 = eq(_T_236, _T_248)
    node _T_250 = mux(_T_221, _T_224, _T_249)
    node _T_251 = and(_T_220, _T_250)
    node _T_252 = and(_T_218, UInt<1>(1))
    node _T_253 = and(_T_252, io.bp[0].control.w)
    node _T_254 = bits(io.bp[0].control.tmatch, 1, 1)
    node _T_255 = geq(io.ea, io.bp[0].address)
    node _T_256 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_257 = xor(_T_255, _T_256)
    node _T_258 = not(io.ea)
    node _T_259 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_260 = bits(io.bp[0].address, 0, 0)
    node _T_261 = and(_T_259, _T_260)
    node _T_262 = bits(io.bp[0].address, 1, 1)
    node _T_263 = and(_T_261, _T_262)
    node _T_264 = bits(io.bp[0].address, 2, 2)
    node _T_265 = and(_T_263, _T_264)
    node _T_266 = cat(_T_261, _T_259)
    node _T_267 = cat(_T_265, _T_263)
    node _T_268 = cat(_T_267, _T_266)
    node _T_269 = or(_T_258, _T_268)
    node _T_270 = not(io.bp[0].address)
    node _T_271 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_272 = bits(io.bp[0].address, 0, 0)
    node _T_273 = and(_T_271, _T_272)
    node _T_274 = bits(io.bp[0].address, 1, 1)
    node _T_275 = and(_T_273, _T_274)
    node _T_276 = bits(io.bp[0].address, 2, 2)
    node _T_277 = and(_T_275, _T_276)
    node _T_278 = cat(_T_273, _T_271)
    node _T_279 = cat(_T_277, _T_275)
    node _T_280 = cat(_T_279, _T_278)
    node _T_281 = or(_T_270, _T_280)
    node _T_282 = eq(_T_269, _T_281)
    node _T_283 = mux(_T_254, _T_257, _T_282)
    node _T_284 = and(_T_253, _T_283)
    node _T_285 = and(_T_218, UInt<1>(1))
    node _T_286 = and(_T_285, io.bp[0].control.x)
    node _T_287 = bits(io.bp[0].control.tmatch, 1, 1)
    node _T_288 = geq(io.pc, io.bp[0].address)
    node _T_289 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_290 = xor(_T_288, _T_289)
    node _T_291 = not(io.pc)
    node _T_292 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_293 = bits(io.bp[0].address, 0, 0)
    node _T_294 = and(_T_292, _T_293)
    node _T_295 = bits(io.bp[0].address, 1, 1)
    node _T_296 = and(_T_294, _T_295)
    node _T_297 = bits(io.bp[0].address, 2, 2)
    node _T_298 = and(_T_296, _T_297)
    node _T_299 = cat(_T_294, _T_292)
    node _T_300 = cat(_T_298, _T_296)
    node _T_301 = cat(_T_300, _T_299)
    node _T_302 = or(_T_291, _T_301)
    node _T_303 = not(io.bp[0].address)
    node _T_304 = bits(io.bp[0].control.tmatch, 0, 0)
    node _T_305 = bits(io.bp[0].address, 0, 0)
    node _T_306 = and(_T_304, _T_305)
    node _T_307 = bits(io.bp[0].address, 1, 1)
    node _T_308 = and(_T_306, _T_307)
    node _T_309 = bits(io.bp[0].address, 2, 2)
    node _T_310 = and(_T_308, _T_309)
    node _T_311 = cat(_T_306, _T_304)
    node _T_312 = cat(_T_310, _T_308)
    node _T_313 = cat(_T_312, _T_311)
    node _T_314 = or(_T_303, _T_313)
    node _T_315 = eq(_T_302, _T_314)
    node _T_316 = mux(_T_287, _T_290, _T_315)
    node _T_317 = and(_T_286, _T_316)
    node _T_319 = eq(io.bp[0].control.chain, UInt<1>(0))
    node _T_320 = and(_T_319, _T_251)
    when _T_320 : 
{
      node _T_322 = eq(io.bp[0].control.action, UInt<1>(0))
      io.xcpt_ld <= _T_322
      io.debug_ld <= io.bp[0].control.action
      skip
}
    node _T_323 = and(_T_319, _T_284)
    when _T_323 : 
{
      node _T_325 = eq(io.bp[0].control.action, UInt<1>(0))
      io.xcpt_st <= _T_325
      io.debug_st <= io.bp[0].control.action
      skip
}
    node _T_326 = and(_T_319, _T_317)
    when _T_326 : 
{
      node _T_328 = eq(io.bp[0].control.action, UInt<1>(0))
      io.xcpt_if <= _T_328
      io.debug_if <= io.bp[0].control.action
      skip
}
    node _T_329 = or(_T_319, _T_251)
    node _T_330 = or(_T_319, _T_284)
    node _T_331 = or(_T_319, _T_317)
  module ALU : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip dw : UInt<1>,  flip fn : UInt<4>,  flip in2 : UInt<64>,  flip in1 : UInt<64>, out : UInt<64>, adder_out : UInt<64>, cmp_out : UInt<1>}
    io is invalid
    io is invalid
    node _T_16 = bits(io.fn, 3, 3)
    node _T_17 = not(io.in2)
    node in2_inv = mux(_T_16, _T_17, io.in2)
    node in1_xor_in2 = xor(io.in1, in2_inv)
    node _T_18 = add(io.in1, in2_inv)
    node _T_19 = tail(_T_18, 1)
    node _T_20 = bits(io.fn, 3, 3)
    node _T_21 = add(_T_19, _T_20)
    node _T_22 = tail(_T_21, 1)
    io.adder_out <= _T_22
    node _T_23 = bits(io.fn, 0, 0)
    node _T_24 = bits(io.fn, 3, 3)
    node _T_26 = eq(_T_24, UInt<1>(0))
    node _T_28 = eq(in1_xor_in2, UInt<1>(0))
    node _T_29 = bits(io.in1, 63, 63)
    node _T_30 = bits(io.in2, 63, 63)
    node _T_31 = eq(_T_29, _T_30)
    node _T_32 = bits(io.adder_out, 63, 63)
    node _T_33 = bits(io.fn, 1, 1)
    node _T_34 = bits(io.in2, 63, 63)
    node _T_35 = bits(io.in1, 63, 63)
    node _T_36 = mux(_T_33, _T_34, _T_35)
    node _T_37 = mux(_T_31, _T_32, _T_36)
    node _T_38 = mux(_T_26, _T_28, _T_37)
    node _T_39 = xor(_T_23, _T_38)
    io.cmp_out <= _T_39
    node _T_40 = bits(io.fn, 3, 3)
    node _T_41 = bits(io.in1, 31, 31)
    node _T_42 = and(_T_40, _T_41)
    node _T_43 = bits(_T_42, 0, 0)
    node _T_46 = mux(_T_43, UInt<32>(4294967295), UInt<32>(0))
    node _T_48 = eq(io.dw, UInt<1>(1))
    node _T_49 = bits(io.in1, 63, 32)
    node _T_50 = mux(_T_48, _T_49, _T_46)
    node _T_51 = bits(io.in2, 5, 5)
    node _T_53 = eq(io.dw, UInt<1>(1))
    node _T_54 = and(_T_51, _T_53)
    node _T_55 = bits(io.in2, 4, 0)
    node shamt = cat(_T_54, _T_55)
    node _T_56 = bits(io.in1, 31, 0)
    node shin_r = cat(_T_50, _T_56)
    node _T_58 = eq(io.fn, UInt<3>(5))
    node _T_60 = eq(io.fn, UInt<4>(11))
    node _T_61 = or(_T_58, _T_60)
    node _T_64 = shl(UInt<32>(4294967295), 32)
    node _T_65 = xor(UInt<64>(18446744073709551615), _T_64)
    node _T_66 = shr(shin_r, 32)
    node _T_67 = and(_T_66, _T_65)
    node _T_68 = bits(shin_r, 31, 0)
    node _T_69 = shl(_T_68, 32)
    node _T_70 = not(_T_65)
    node _T_71 = and(_T_69, _T_70)
    node _T_72 = or(_T_67, _T_71)
    node _T_73 = bits(_T_65, 47, 0)
    node _T_74 = shl(_T_73, 16)
    node _T_75 = xor(_T_65, _T_74)
    node _T_76 = shr(_T_72, 16)
    node _T_77 = and(_T_76, _T_75)
    node _T_78 = bits(_T_72, 47, 0)
    node _T_79 = shl(_T_78, 16)
    node _T_80 = not(_T_75)
    node _T_81 = and(_T_79, _T_80)
    node _T_82 = or(_T_77, _T_81)
    node _T_83 = bits(_T_75, 55, 0)
    node _T_84 = shl(_T_83, 8)
    node _T_85 = xor(_T_75, _T_84)
    node _T_86 = shr(_T_82, 8)
    node _T_87 = and(_T_86, _T_85)
    node _T_88 = bits(_T_82, 55, 0)
    node _T_89 = shl(_T_88, 8)
    node _T_90 = not(_T_85)
    node _T_91 = and(_T_89, _T_90)
    node _T_92 = or(_T_87, _T_91)
    node _T_93 = bits(_T_85, 59, 0)
    node _T_94 = shl(_T_93, 4)
    node _T_95 = xor(_T_85, _T_94)
    node _T_96 = shr(_T_92, 4)
    node _T_97 = and(_T_96, _T_95)
    node _T_98 = bits(_T_92, 59, 0)
    node _T_99 = shl(_T_98, 4)
    node _T_100 = not(_T_95)
    node _T_101 = and(_T_99, _T_100)
    node _T_102 = or(_T_97, _T_101)
    node _T_103 = bits(_T_95, 61, 0)
    node _T_104 = shl(_T_103, 2)
    node _T_105 = xor(_T_95, _T_104)
    node _T_106 = shr(_T_102, 2)
    node _T_107 = and(_T_106, _T_105)
    node _T_108 = bits(_T_102, 61, 0)
    node _T_109 = shl(_T_108, 2)
    node _T_110 = not(_T_105)
    node _T_111 = and(_T_109, _T_110)
    node _T_112 = or(_T_107, _T_111)
    node _T_113 = bits(_T_105, 62, 0)
    node _T_114 = shl(_T_113, 1)
    node _T_115 = xor(_T_105, _T_114)
    node _T_116 = shr(_T_112, 1)
    node _T_117 = and(_T_116, _T_115)
    node _T_118 = bits(_T_112, 62, 0)
    node _T_119 = shl(_T_118, 1)
    node _T_120 = not(_T_115)
    node _T_121 = and(_T_119, _T_120)
    node _T_122 = or(_T_117, _T_121)
    node shin = mux(_T_61, shin_r, _T_122)
    node _T_123 = bits(io.fn, 3, 3)
    node _T_124 = bits(shin, 63, 63)
    node _T_125 = and(_T_123, _T_124)
    node _T_126 = cat(_T_125, shin)
    node _T_127 = asSInt(_T_126)
    node _T_128 = dshr(_T_127, shamt)
    node shout_r = bits(_T_128, 63, 0)
    node _T_131 = shl(UInt<32>(4294967295), 32)
    node _T_132 = xor(UInt<64>(18446744073709551615), _T_131)
    node _T_133 = shr(shout_r, 32)
    node _T_134 = and(_T_133, _T_132)
    node _T_135 = bits(shout_r, 31, 0)
    node _T_136 = shl(_T_135, 32)
    node _T_137 = not(_T_132)
    node _T_138 = and(_T_136, _T_137)
    node _T_139 = or(_T_134, _T_138)
    node _T_140 = bits(_T_132, 47, 0)
    node _T_141 = shl(_T_140, 16)
    node _T_142 = xor(_T_132, _T_141)
    node _T_143 = shr(_T_139, 16)
    node _T_144 = and(_T_143, _T_142)
    node _T_145 = bits(_T_139, 47, 0)
    node _T_146 = shl(_T_145, 16)
    node _T_147 = not(_T_142)
    node _T_148 = and(_T_146, _T_147)
    node _T_149 = or(_T_144, _T_148)
    node _T_150 = bits(_T_142, 55, 0)
    node _T_151 = shl(_T_150, 8)
    node _T_152 = xor(_T_142, _T_151)
    node _T_153 = shr(_T_149, 8)
    node _T_154 = and(_T_153, _T_152)
    node _T_155 = bits(_T_149, 55, 0)
    node _T_156 = shl(_T_155, 8)
    node _T_157 = not(_T_152)
    node _T_158 = and(_T_156, _T_157)
    node _T_159 = or(_T_154, _T_158)
    node _T_160 = bits(_T_152, 59, 0)
    node _T_161 = shl(_T_160, 4)
    node _T_162 = xor(_T_152, _T_161)
    node _T_163 = shr(_T_159, 4)
    node _T_164 = and(_T_163, _T_162)
    node _T_165 = bits(_T_159, 59, 0)
    node _T_166 = shl(_T_165, 4)
    node _T_167 = not(_T_162)
    node _T_168 = and(_T_166, _T_167)
    node _T_169 = or(_T_164, _T_168)
    node _T_170 = bits(_T_162, 61, 0)
    node _T_171 = shl(_T_170, 2)
    node _T_172 = xor(_T_162, _T_171)
    node _T_173 = shr(_T_169, 2)
    node _T_174 = and(_T_173, _T_172)
    node _T_175 = bits(_T_169, 61, 0)
    node _T_176 = shl(_T_175, 2)
    node _T_177 = not(_T_172)
    node _T_178 = and(_T_176, _T_177)
    node _T_179 = or(_T_174, _T_178)
    node _T_180 = bits(_T_172, 62, 0)
    node _T_181 = shl(_T_180, 1)
    node _T_182 = xor(_T_172, _T_181)
    node _T_183 = shr(_T_179, 1)
    node _T_184 = and(_T_183, _T_182)
    node _T_185 = bits(_T_179, 62, 0)
    node _T_186 = shl(_T_185, 1)
    node _T_187 = not(_T_182)
    node _T_188 = and(_T_186, _T_187)
    node shout_l = or(_T_184, _T_188)
    node _T_190 = eq(io.fn, UInt<3>(5))
    node _T_192 = eq(io.fn, UInt<4>(11))
    node _T_193 = or(_T_190, _T_192)
    node _T_195 = mux(_T_193, shout_r, UInt<1>(0))
    node _T_197 = eq(io.fn, UInt<1>(1))
    node _T_199 = mux(_T_197, shout_l, UInt<1>(0))
    node shout = or(_T_195, _T_199)
    node _T_201 = eq(io.fn, UInt<3>(4))
    node _T_203 = eq(io.fn, UInt<3>(6))
    node _T_204 = or(_T_201, _T_203)
    node _T_206 = mux(_T_204, in1_xor_in2, UInt<1>(0))
    node _T_208 = eq(io.fn, UInt<3>(6))
    node _T_210 = eq(io.fn, UInt<3>(7))
    node _T_211 = or(_T_208, _T_210)
    node _T_212 = and(io.in1, io.in2)
    node _T_214 = mux(_T_211, _T_212, UInt<1>(0))
    node logic = or(_T_206, _T_214)
    node _T_216 = eq(io.fn, UInt<2>(2))
    node _T_218 = eq(io.fn, UInt<2>(3))
    node _T_219 = or(_T_216, _T_218)
    node _T_221 = geq(io.fn, UInt<4>(12))
    node _T_222 = or(_T_219, _T_221)
    node _T_223 = and(_T_222, io.cmp_out)
    node _T_224 = or(_T_223, logic)
    node shift_logic = or(_T_224, shout)
    node _T_226 = eq(io.fn, UInt<1>(0))
    node _T_228 = eq(io.fn, UInt<4>(10))
    node _T_229 = or(_T_226, _T_228)
    node out = mux(_T_229, io.adder_out, shift_logic)
    io.out <= out
    node _T_231 = eq(io.dw, UInt<1>(0))
    when _T_231 : 
{
      node _T_232 = bits(out, 31, 31)
      node _T_233 = bits(_T_232, 0, 0)
      node _T_236 = mux(_T_233, UInt<32>(4294967295), UInt<32>(0))
      node _T_237 = bits(out, 31, 0)
      node _T_238 = cat(_T_236, _T_237)
      io.out <= _T_238
      skip
}
  module MulDiv : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip req : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {fn : UInt<4>, dw : UInt<1>, in1 : UInt<64>, in2 : UInt<64>, tag : UInt<5>}},  flip kill : UInt<1>, resp : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : {data : UInt<64>, tag : UInt<5>}}}
    io is invalid
    io is invalid
    regreset state : UInt<3>, clock, reset_wky, UInt<3>(0)
    reg req : {fn : UInt<4>, dw : UInt<1>, in1 : UInt<64>, in2 : UInt<64>, tag : UInt<5>}, clock 
    reg count : UInt<7>, clock 
    reg neg_out : UInt<1>, clock 
    reg isMul : UInt<1>, clock 
    reg isHi : UInt<1>, clock 
    reg divisor : UInt<65>, clock 
    reg remainder : UInt<130>, clock 
    node _T_79 = and(io.req.bits_wky.fn, UInt<4>(4))
    node _T_81 = eq(_T_79, UInt<4>(0))
    node _T_83 = and(io.req.bits_wky.fn, UInt<4>(8))
    node _T_85 = eq(_T_83, UInt<4>(8))
    node _T_87 = or(UInt<1>(0), _T_81)
    node _T_88 = or(_T_87, _T_85)
    node _T_90 = and(io.req.bits_wky.fn, UInt<4>(5))
    node _T_92 = eq(_T_90, UInt<4>(1))
    node _T_94 = and(io.req.bits_wky.fn, UInt<4>(2))
    node _T_96 = eq(_T_94, UInt<4>(2))
    node _T_98 = or(UInt<1>(0), _T_92)
    node _T_99 = or(_T_98, _T_96)
    node _T_100 = or(_T_99, _T_85)
    node _T_102 = and(io.req.bits_wky.fn, UInt<4>(9))
    node _T_104 = eq(_T_102, UInt<4>(0))
    node _T_106 = and(io.req.bits_wky.fn, UInt<4>(3))
    node _T_108 = eq(_T_106, UInt<4>(0))
    node _T_110 = or(UInt<1>(0), _T_104)
    node _T_111 = or(_T_110, _T_81)
    node _T_112 = or(_T_111, _T_108)
    node _T_114 = or(UInt<1>(0), _T_104)
    node _T_115 = or(_T_114, _T_81)
    node cmdMul = bits(_T_88, 0, 0)
    node cmdHi = bits(_T_100, 0, 0)
    node lhsSigned = bits(_T_112, 0, 0)
    node rhsSigned = bits(_T_115, 0, 0)
    node _T_118 = eq(io.req.bits_wky.dw, UInt<1>(0))
    node _T_119 = and(UInt<1>(1), _T_118)
    node _T_120 = bits(io.req.bits_wky.in1, 31, 31)
    node _T_121 = bits(io.req.bits_wky.in1, 63, 63)
    node _T_122 = mux(_T_119, _T_120, _T_121)
    node lhs_sign = and(lhsSigned, _T_122)
    node _T_123 = bits(lhs_sign, 0, 0)
    node _T_126 = mux(_T_123, UInt<32>(4294967295), UInt<32>(0))
    node _T_127 = bits(io.req.bits_wky.in1, 63, 32)
    node _T_128 = mux(_T_119, _T_126, _T_127)
    node _T_129 = bits(io.req.bits_wky.in1, 31, 0)
    node lhs_in = cat(_T_128, _T_129)
    node _T_132 = eq(io.req.bits_wky.dw, UInt<1>(0))
    node _T_133 = and(UInt<1>(1), _T_132)
    node _T_134 = bits(io.req.bits_wky.in2, 31, 31)
    node _T_135 = bits(io.req.bits_wky.in2, 63, 63)
    node _T_136 = mux(_T_133, _T_134, _T_135)
    node rhs_sign = and(rhsSigned, _T_136)
    node _T_137 = bits(rhs_sign, 0, 0)
    node _T_140 = mux(_T_137, UInt<32>(4294967295), UInt<32>(0))
    node _T_141 = bits(io.req.bits_wky.in2, 63, 32)
    node _T_142 = mux(_T_133, _T_140, _T_141)
    node _T_143 = bits(io.req.bits_wky.in2, 31, 0)
    node rhs_in = cat(_T_142, _T_143)
    node _T_144 = bits(remainder, 128, 64)
    node _T_145 = sub(_T_144, divisor)
    node _T_146 = asUInt(_T_145)
    node subtractor = tail(_T_146, 1)
    node _T_147 = bits(remainder, 63, 0)
    node _T_149 = sub(UInt<1>(0), _T_147)
    node _T_150 = asUInt(_T_149)
    node negated_remainder = tail(_T_150, 1)
    node _T_151 = eq(state, UInt<3>(1))
    when _T_151 : 
{
      node _T_152 = bits(remainder, 63, 63)
      node _T_153 = or(_T_152, isMul)
      when _T_153 : 
{
        remainder <= negated_remainder
        skip
}
      node _T_154 = bits(divisor, 63, 63)
      node _T_155 = or(_T_154, isMul)
      when _T_155 : 
{
        divisor <= subtractor
        skip
}
      state <= UInt<3>(2)
      skip
}
    node _T_156 = eq(state, UInt<3>(4))
    when _T_156 : 
{
      remainder <= negated_remainder
      state <= UInt<3>(5)
      skip
}
    node _T_157 = eq(state, UInt<3>(3))
    when _T_157 : 
{
      node _T_158 = bits(remainder, 128, 65)
      remainder <= _T_158
      node _T_159 = mux(neg_out, UInt<3>(4), UInt<3>(5))
      state <= _T_159
      skip
}
    node _T_160 = eq(state, UInt<3>(2))
    node _T_161 = and(_T_160, isMul)
    when _T_161 : 
{
      node _T_162 = bits(remainder, 129, 65)
      node _T_163 = bits(remainder, 63, 0)
      node _T_164 = cat(_T_162, _T_163)
      node _T_165 = bits(_T_164, 63, 0)
      node _T_166 = bits(_T_164, 128, 64)
      node _T_167 = asSInt(_T_166)
      node _T_168 = asSInt(divisor)
      node _T_169 = bits(_T_165, 7, 0)
      node _M_170 = asSInt(_T_169)
      node _T_170 = mul(_T_168, _M_170)
      node _T_171 = add(_T_170, _T_167)
      node _T_172 = tail(_T_171, 1)
      node _T_173 = asSInt(_T_172)
      node _T_174 = bits(_T_165, 63, 8)
      node _T_175 = asUInt(_T_173)
      node _T_176 = cat(_T_175, _T_174)
      node _T_179 = mul(count, UInt<4>(8))
      node _T_180 = bits(_T_179, 5, 0)
      node _T_181 = dshr(asSInt(UInt<65>(18446744073709551616)), _T_180)
      node _T_182 = bits(_T_181, 63, 0)
      node _T_185 = neq(count, UInt<3>(7))
      node _T_186 = and(UInt<1>(1), _T_185)
      node _T_188 = neq(count, UInt<1>(0))
      node _T_189 = and(_T_186, _T_188)
      node _T_191 = eq(isHi, UInt<1>(0))
      node _T_192 = and(_T_189, _T_191)
      node _T_193 = not(_T_182)
      node _T_194 = and(_T_165, _T_193)
      node _T_196 = eq(_T_194, UInt<1>(0))
      node _T_197 = and(_T_192, _T_196)
      node _T_200 = mul(count, UInt<4>(8))
      node _T_201 = sub(UInt<7>(64), _T_200)
      node _T_202 = asUInt(_T_201)
      node _T_203 = tail(_T_202, 1)
      node _T_204 = bits(_T_203, 5, 0)
      node _T_205 = dshr(_T_164, _T_204)
      node _T_206 = bits(_T_176, 128, 64)
      node _T_207 = mux(_T_197, _T_205, _T_176)
      node _T_208 = bits(_T_207, 63, 0)
      node _T_209 = cat(_T_206, _T_208)
      node _T_210 = shr(_T_209, 64)
      node _T_212 = bits(_T_209, 63, 0)
      node _T_213 = cat(_T_210, UInt<1>(0))
      node _T_214 = cat(_T_213, _T_212)
      remainder <= _T_214
      node _T_216 = add(count, UInt<1>(1))
      node _T_217 = tail(_T_216, 1)
      count <= _T_217
      node _T_219 = eq(count, UInt<3>(7))
      node _T_220 = or(_T_197, _T_219)
      when _T_220 : 
{
        node _T_221 = mux(isHi, UInt<3>(3), UInt<3>(5))
        state <= _T_221
        skip
}
      skip
}
    node _T_222 = eq(state, UInt<3>(2))
    node _T_224 = eq(isMul, UInt<1>(0))
    node _T_225 = and(_T_222, _T_224)
    when _T_225 : 
{
      node _T_226 = bits(subtractor, 64, 64)
      node _T_227 = bits(remainder, 127, 64)
      node _T_228 = bits(subtractor, 63, 0)
      node _T_229 = mux(_T_226, _T_227, _T_228)
      node _T_230 = bits(remainder, 63, 0)
      node _T_232 = eq(_T_226, UInt<1>(0))
      node _T_233 = cat(_T_229, _T_230)
      node _T_234 = cat(_T_233, _T_232)
      remainder <= _T_234
      node _T_236 = eq(count, UInt<7>(64))
      when _T_236 : 
{
        node _T_237 = mux(neg_out, UInt<3>(4), UInt<3>(5))
        node _T_238 = mux(isHi, UInt<3>(3), _T_237)
        state <= _T_238
        skip
}
      node _T_240 = add(count, UInt<1>(1))
      node _T_241 = tail(_T_240, 1)
      count <= _T_241
      node _T_243 = eq(count, UInt<1>(0))
      node _T_244 = bits(subtractor, 64, 64)
      node _T_246 = eq(_T_244, UInt<1>(0))
      node _T_247 = and(_T_243, _T_246)
      node _T_248 = bits(divisor, 63, 0)
      node _T_249 = bits(_T_248, 63, 32)
      node _T_250 = bits(_T_248, 31, 0)
      node _T_252 = neq(_T_249, UInt<1>(0))
      node _T_253 = bits(_T_249, 31, 16)
      node _T_254 = bits(_T_249, 15, 0)
      node _T_256 = neq(_T_253, UInt<1>(0))
      node _T_257 = bits(_T_253, 15, 8)
      node _T_258 = bits(_T_253, 7, 0)
      node _T_260 = neq(_T_257, UInt<1>(0))
      node _T_261 = bits(_T_257, 7, 4)
      node _T_262 = bits(_T_257, 3, 0)
      node _T_264 = neq(_T_261, UInt<1>(0))
      node _T_265 = bits(_T_261, 3, 3)
      node _T_267 = bits(_T_261, 2, 2)
      node _T_269 = bits(_T_261, 1, 1)
      node _T_270 = mux(_T_267, UInt<2>(2), _T_269)
      node _T_271 = mux(_T_265, UInt<2>(3), _T_270)
      node _T_272 = bits(_T_262, 3, 3)
      node _T_274 = bits(_T_262, 2, 2)
      node _T_276 = bits(_T_262, 1, 1)
      node _T_277 = mux(_T_274, UInt<2>(2), _T_276)
      node _T_278 = mux(_T_272, UInt<2>(3), _T_277)
      node _T_279 = mux(_T_264, _T_271, _T_278)
      node _T_280 = cat(_T_264, _T_279)
      node _T_281 = bits(_T_258, 7, 4)
      node _T_282 = bits(_T_258, 3, 0)
      node _T_284 = neq(_T_281, UInt<1>(0))
      node _T_285 = bits(_T_281, 3, 3)
      node _T_287 = bits(_T_281, 2, 2)
      node _T_289 = bits(_T_281, 1, 1)
      node _T_290 = mux(_T_287, UInt<2>(2), _T_289)
      node _T_291 = mux(_T_285, UInt<2>(3), _T_290)
      node _T_292 = bits(_T_282, 3, 3)
      node _T_294 = bits(_T_282, 2, 2)
      node _T_296 = bits(_T_282, 1, 1)
      node _T_297 = mux(_T_294, UInt<2>(2), _T_296)
      node _T_298 = mux(_T_292, UInt<2>(3), _T_297)
      node _T_299 = mux(_T_284, _T_291, _T_298)
      node _T_300 = cat(_T_284, _T_299)
      node _T_301 = mux(_T_260, _T_280, _T_300)
      node _T_302 = cat(_T_260, _T_301)
      node _T_303 = bits(_T_254, 15, 8)
      node _T_304 = bits(_T_254, 7, 0)
      node _T_306 = neq(_T_303, UInt<1>(0))
      node _T_307 = bits(_T_303, 7, 4)
      node _T_308 = bits(_T_303, 3, 0)
      node _T_310 = neq(_T_307, UInt<1>(0))
      node _T_311 = bits(_T_307, 3, 3)
      node _T_313 = bits(_T_307, 2, 2)
      node _T_315 = bits(_T_307, 1, 1)
      node _T_316 = mux(_T_313, UInt<2>(2), _T_315)
      node _T_317 = mux(_T_311, UInt<2>(3), _T_316)
      node _T_318 = bits(_T_308, 3, 3)
      node _T_320 = bits(_T_308, 2, 2)
      node _T_322 = bits(_T_308, 1, 1)
      node _T_323 = mux(_T_320, UInt<2>(2), _T_322)
      node _T_324 = mux(_T_318, UInt<2>(3), _T_323)
      node _T_325 = mux(_T_310, _T_317, _T_324)
      node _T_326 = cat(_T_310, _T_325)
      node _T_327 = bits(_T_304, 7, 4)
      node _T_328 = bits(_T_304, 3, 0)
      node _T_330 = neq(_T_327, UInt<1>(0))
      node _T_331 = bits(_T_327, 3, 3)
      node _T_333 = bits(_T_327, 2, 2)
      node _T_335 = bits(_T_327, 1, 1)
      node _T_336 = mux(_T_333, UInt<2>(2), _T_335)
      node _T_337 = mux(_T_331, UInt<2>(3), _T_336)
      node _T_338 = bits(_T_328, 3, 3)
      node _T_340 = bits(_T_328, 2, 2)
      node _T_342 = bits(_T_328, 1, 1)
      node _T_343 = mux(_T_340, UInt<2>(2), _T_342)
      node _T_344 = mux(_T_338, UInt<2>(3), _T_343)
      node _T_345 = mux(_T_330, _T_337, _T_344)
      node _T_346 = cat(_T_330, _T_345)
      node _T_347 = mux(_T_306, _T_326, _T_346)
      node _T_348 = cat(_T_306, _T_347)
      node _T_349 = mux(_T_256, _T_302, _T_348)
      node _T_350 = cat(_T_256, _T_349)
      node _T_351 = bits(_T_250, 31, 16)
      node _T_352 = bits(_T_250, 15, 0)
      node _T_354 = neq(_T_351, UInt<1>(0))
      node _T_355 = bits(_T_351, 15, 8)
      node _T_356 = bits(_T_351, 7, 0)
      node _T_358 = neq(_T_355, UInt<1>(0))
      node _T_359 = bits(_T_355, 7, 4)
      node _T_360 = bits(_T_355, 3, 0)
      node _T_362 = neq(_T_359, UInt<1>(0))
      node _T_363 = bits(_T_359, 3, 3)
      node _T_365 = bits(_T_359, 2, 2)
      node _T_367 = bits(_T_359, 1, 1)
      node _T_368 = mux(_T_365, UInt<2>(2), _T_367)
      node _T_369 = mux(_T_363, UInt<2>(3), _T_368)
      node _T_370 = bits(_T_360, 3, 3)
      node _T_372 = bits(_T_360, 2, 2)
      node _T_374 = bits(_T_360, 1, 1)
      node _T_375 = mux(_T_372, UInt<2>(2), _T_374)
      node _T_376 = mux(_T_370, UInt<2>(3), _T_375)
      node _T_377 = mux(_T_362, _T_369, _T_376)
      node _T_378 = cat(_T_362, _T_377)
      node _T_379 = bits(_T_356, 7, 4)
      node _T_380 = bits(_T_356, 3, 0)
      node _T_382 = neq(_T_379, UInt<1>(0))
      node _T_383 = bits(_T_379, 3, 3)
      node _T_385 = bits(_T_379, 2, 2)
      node _T_387 = bits(_T_379, 1, 1)
      node _T_388 = mux(_T_385, UInt<2>(2), _T_387)
      node _T_389 = mux(_T_383, UInt<2>(3), _T_388)
      node _T_390 = bits(_T_380, 3, 3)
      node _T_392 = bits(_T_380, 2, 2)
      node _T_394 = bits(_T_380, 1, 1)
      node _T_395 = mux(_T_392, UInt<2>(2), _T_394)
      node _T_396 = mux(_T_390, UInt<2>(3), _T_395)
      node _T_397 = mux(_T_382, _T_389, _T_396)
      node _T_398 = cat(_T_382, _T_397)
      node _T_399 = mux(_T_358, _T_378, _T_398)
      node _T_400 = cat(_T_358, _T_399)
      node _T_401 = bits(_T_352, 15, 8)
      node _T_402 = bits(_T_352, 7, 0)
      node _T_404 = neq(_T_401, UInt<1>(0))
      node _T_405 = bits(_T_401, 7, 4)
      node _T_406 = bits(_T_401, 3, 0)
      node _T_408 = neq(_T_405, UInt<1>(0))
      node _T_409 = bits(_T_405, 3, 3)
      node _T_411 = bits(_T_405, 2, 2)
      node _T_413 = bits(_T_405, 1, 1)
      node _T_414 = mux(_T_411, UInt<2>(2), _T_413)
      node _T_415 = mux(_T_409, UInt<2>(3), _T_414)
      node _T_416 = bits(_T_406, 3, 3)
      node _T_418 = bits(_T_406, 2, 2)
      node _T_420 = bits(_T_406, 1, 1)
      node _T_421 = mux(_T_418, UInt<2>(2), _T_420)
      node _T_422 = mux(_T_416, UInt<2>(3), _T_421)
      node _T_423 = mux(_T_408, _T_415, _T_422)
      node _T_424 = cat(_T_408, _T_423)
      node _T_425 = bits(_T_402, 7, 4)
      node _T_426 = bits(_T_402, 3, 0)
      node _T_428 = neq(_T_425, UInt<1>(0))
      node _T_429 = bits(_T_425, 3, 3)
      node _T_431 = bits(_T_425, 2, 2)
      node _T_433 = bits(_T_425, 1, 1)
      node _T_434 = mux(_T_431, UInt<2>(2), _T_433)
      node _T_435 = mux(_T_429, UInt<2>(3), _T_434)
      node _T_436 = bits(_T_426, 3, 3)
      node _T_438 = bits(_T_426, 2, 2)
      node _T_440 = bits(_T_426, 1, 1)
      node _T_441 = mux(_T_438, UInt<2>(2), _T_440)
      node _T_442 = mux(_T_436, UInt<2>(3), _T_441)
      node _T_443 = mux(_T_428, _T_435, _T_442)
      node _T_444 = cat(_T_428, _T_443)
      node _T_445 = mux(_T_404, _T_424, _T_444)
      node _T_446 = cat(_T_404, _T_445)
      node _T_447 = mux(_T_354, _T_400, _T_446)
      node _T_448 = cat(_T_354, _T_447)
      node _T_449 = mux(_T_252, _T_350, _T_448)
      node _T_450 = cat(_T_252, _T_449)
      node _T_451 = bits(remainder, 63, 0)
      node _T_452 = bits(_T_451, 63, 32)
      node _T_453 = bits(_T_451, 31, 0)
      node _T_455 = neq(_T_452, UInt<1>(0))
      node _T_456 = bits(_T_452, 31, 16)
      node _T_457 = bits(_T_452, 15, 0)
      node _T_459 = neq(_T_456, UInt<1>(0))
      node _T_460 = bits(_T_456, 15, 8)
      node _T_461 = bits(_T_456, 7, 0)
      node _T_463 = neq(_T_460, UInt<1>(0))
      node _T_464 = bits(_T_460, 7, 4)
      node _T_465 = bits(_T_460, 3, 0)
      node _T_467 = neq(_T_464, UInt<1>(0))
      node _T_468 = bits(_T_464, 3, 3)
      node _T_470 = bits(_T_464, 2, 2)
      node _T_472 = bits(_T_464, 1, 1)
      node _T_473 = mux(_T_470, UInt<2>(2), _T_472)
      node _T_474 = mux(_T_468, UInt<2>(3), _T_473)
      node _T_475 = bits(_T_465, 3, 3)
      node _T_477 = bits(_T_465, 2, 2)
      node _T_479 = bits(_T_465, 1, 1)
      node _T_480 = mux(_T_477, UInt<2>(2), _T_479)
      node _T_481 = mux(_T_475, UInt<2>(3), _T_480)
      node _T_482 = mux(_T_467, _T_474, _T_481)
      node _T_483 = cat(_T_467, _T_482)
      node _T_484 = bits(_T_461, 7, 4)
      node _T_485 = bits(_T_461, 3, 0)
      node _T_487 = neq(_T_484, UInt<1>(0))
      node _T_488 = bits(_T_484, 3, 3)
      node _T_490 = bits(_T_484, 2, 2)
      node _T_492 = bits(_T_484, 1, 1)
      node _T_493 = mux(_T_490, UInt<2>(2), _T_492)
      node _T_494 = mux(_T_488, UInt<2>(3), _T_493)
      node _T_495 = bits(_T_485, 3, 3)
      node _T_497 = bits(_T_485, 2, 2)
      node _T_499 = bits(_T_485, 1, 1)
      node _T_500 = mux(_T_497, UInt<2>(2), _T_499)
      node _T_501 = mux(_T_495, UInt<2>(3), _T_500)
      node _T_502 = mux(_T_487, _T_494, _T_501)
      node _T_503 = cat(_T_487, _T_502)
      node _T_504 = mux(_T_463, _T_483, _T_503)
      node _T_505 = cat(_T_463, _T_504)
      node _T_506 = bits(_T_457, 15, 8)
      node _T_507 = bits(_T_457, 7, 0)
      node _T_509 = neq(_T_506, UInt<1>(0))
      node _T_510 = bits(_T_506, 7, 4)
      node _T_511 = bits(_T_506, 3, 0)
      node _T_513 = neq(_T_510, UInt<1>(0))
      node _T_514 = bits(_T_510, 3, 3)
      node _T_516 = bits(_T_510, 2, 2)
      node _T_518 = bits(_T_510, 1, 1)
      node _T_519 = mux(_T_516, UInt<2>(2), _T_518)
      node _T_520 = mux(_T_514, UInt<2>(3), _T_519)
      node _T_521 = bits(_T_511, 3, 3)
      node _T_523 = bits(_T_511, 2, 2)
      node _T_525 = bits(_T_511, 1, 1)
      node _T_526 = mux(_T_523, UInt<2>(2), _T_525)
      node _T_527 = mux(_T_521, UInt<2>(3), _T_526)
      node _T_528 = mux(_T_513, _T_520, _T_527)
      node _T_529 = cat(_T_513, _T_528)
      node _T_530 = bits(_T_507, 7, 4)
      node _T_531 = bits(_T_507, 3, 0)
      node _T_533 = neq(_T_530, UInt<1>(0))
      node _T_534 = bits(_T_530, 3, 3)
      node _T_536 = bits(_T_530, 2, 2)
      node _T_538 = bits(_T_530, 1, 1)
      node _T_539 = mux(_T_536, UInt<2>(2), _T_538)
      node _T_540 = mux(_T_534, UInt<2>(3), _T_539)
      node _T_541 = bits(_T_531, 3, 3)
      node _T_543 = bits(_T_531, 2, 2)
      node _T_545 = bits(_T_531, 1, 1)
      node _T_546 = mux(_T_543, UInt<2>(2), _T_545)
      node _T_547 = mux(_T_541, UInt<2>(3), _T_546)
      node _T_548 = mux(_T_533, _T_540, _T_547)
      node _T_549 = cat(_T_533, _T_548)
      node _T_550 = mux(_T_509, _T_529, _T_549)
      node _T_551 = cat(_T_509, _T_550)
      node _T_552 = mux(_T_459, _T_505, _T_551)
      node _T_553 = cat(_T_459, _T_552)
      node _T_554 = bits(_T_453, 31, 16)
      node _T_555 = bits(_T_453, 15, 0)
      node _T_557 = neq(_T_554, UInt<1>(0))
      node _T_558 = bits(_T_554, 15, 8)
      node _T_559 = bits(_T_554, 7, 0)
      node _T_561 = neq(_T_558, UInt<1>(0))
      node _T_562 = bits(_T_558, 7, 4)
      node _T_563 = bits(_T_558, 3, 0)
      node _T_565 = neq(_T_562, UInt<1>(0))
      node _T_566 = bits(_T_562, 3, 3)
      node _T_568 = bits(_T_562, 2, 2)
      node _T_570 = bits(_T_562, 1, 1)
      node _T_571 = mux(_T_568, UInt<2>(2), _T_570)
      node _T_572 = mux(_T_566, UInt<2>(3), _T_571)
      node _T_573 = bits(_T_563, 3, 3)
      node _T_575 = bits(_T_563, 2, 2)
      node _T_577 = bits(_T_563, 1, 1)
      node _T_578 = mux(_T_575, UInt<2>(2), _T_577)
      node _T_579 = mux(_T_573, UInt<2>(3), _T_578)
      node _T_580 = mux(_T_565, _T_572, _T_579)
      node _T_581 = cat(_T_565, _T_580)
      node _T_582 = bits(_T_559, 7, 4)
      node _T_583 = bits(_T_559, 3, 0)
      node _T_585 = neq(_T_582, UInt<1>(0))
      node _T_586 = bits(_T_582, 3, 3)
      node _T_588 = bits(_T_582, 2, 2)
      node _T_590 = bits(_T_582, 1, 1)
      node _T_591 = mux(_T_588, UInt<2>(2), _T_590)
      node _T_592 = mux(_T_586, UInt<2>(3), _T_591)
      node _T_593 = bits(_T_583, 3, 3)
      node _T_595 = bits(_T_583, 2, 2)
      node _T_597 = bits(_T_583, 1, 1)
      node _T_598 = mux(_T_595, UInt<2>(2), _T_597)
      node _T_599 = mux(_T_593, UInt<2>(3), _T_598)
      node _T_600 = mux(_T_585, _T_592, _T_599)
      node _T_601 = cat(_T_585, _T_600)
      node _T_602 = mux(_T_561, _T_581, _T_601)
      node _T_603 = cat(_T_561, _T_602)
      node _T_604 = bits(_T_555, 15, 8)
      node _T_605 = bits(_T_555, 7, 0)
      node _T_607 = neq(_T_604, UInt<1>(0))
      node _T_608 = bits(_T_604, 7, 4)
      node _T_609 = bits(_T_604, 3, 0)
      node _T_611 = neq(_T_608, UInt<1>(0))
      node _T_612 = bits(_T_608, 3, 3)
      node _T_614 = bits(_T_608, 2, 2)
      node _T_616 = bits(_T_608, 1, 1)
      node _T_617 = mux(_T_614, UInt<2>(2), _T_616)
      node _T_618 = mux(_T_612, UInt<2>(3), _T_617)
      node _T_619 = bits(_T_609, 3, 3)
      node _T_621 = bits(_T_609, 2, 2)
      node _T_623 = bits(_T_609, 1, 1)
      node _T_624 = mux(_T_621, UInt<2>(2), _T_623)
      node _T_625 = mux(_T_619, UInt<2>(3), _T_624)
      node _T_626 = mux(_T_611, _T_618, _T_625)
      node _T_627 = cat(_T_611, _T_626)
      node _T_628 = bits(_T_605, 7, 4)
      node _T_629 = bits(_T_605, 3, 0)
      node _T_631 = neq(_T_628, UInt<1>(0))
      node _T_632 = bits(_T_628, 3, 3)
      node _T_634 = bits(_T_628, 2, 2)
      node _T_636 = bits(_T_628, 1, 1)
      node _T_637 = mux(_T_634, UInt<2>(2), _T_636)
      node _T_638 = mux(_T_632, UInt<2>(3), _T_637)
      node _T_639 = bits(_T_629, 3, 3)
      node _T_641 = bits(_T_629, 2, 2)
      node _T_643 = bits(_T_629, 1, 1)
      node _T_644 = mux(_T_641, UInt<2>(2), _T_643)
      node _T_645 = mux(_T_639, UInt<2>(3), _T_644)
      node _T_646 = mux(_T_631, _T_638, _T_645)
      node _T_647 = cat(_T_631, _T_646)
      node _T_648 = mux(_T_607, _T_627, _T_647)
      node _T_649 = cat(_T_607, _T_648)
      node _T_650 = mux(_T_557, _T_603, _T_649)
      node _T_651 = cat(_T_557, _T_650)
      node _T_652 = mux(_T_455, _T_553, _T_651)
      node _T_653 = cat(_T_455, _T_652)
      node _T_655 = add(UInt<6>(63), _T_450)
      node _T_656 = tail(_T_655, 1)
      node _T_657 = sub(_T_656, _T_653)
      node _T_658 = asUInt(_T_657)
      node _T_659 = tail(_T_658, 1)
      node _T_660 = gt(_T_450, _T_653)
      node _T_662 = eq(count, UInt<1>(0))
      node _T_664 = eq(_T_247, UInt<1>(0))
      node _T_665 = and(_T_662, _T_664)
      node _T_667 = geq(_T_659, UInt<1>(1))
      node _T_668 = or(_T_667, _T_660)
      node _T_669 = and(_T_665, _T_668)
      when _T_669 : 
{
        node _T_671 = mux(_T_660, UInt<6>(63), _T_659)
        node _T_672 = shr(_T_671, 0)
        node _T_673 = shl(_T_672, 0)
        node _T_674 = bits(remainder, 63, 0)
        node _T_675 = dshl(_T_674, _T_673)
        remainder <= _T_675
        count <= _T_672
        skip
}
      node _T_677 = eq(isHi, UInt<1>(0))
      node _T_678 = and(_T_247, _T_677)
      when _T_678 : 
{
        neg_out <= UInt<1>(0)
        skip
}
      skip
}
    node _T_680 = and(io.resp.ready, io.resp.valid)
    node _T_681 = or(_T_680, io.kill)
    when _T_681 : 
{
      state <= UInt<3>(0)
      skip
}
    node _T_682 = and(io.req.ready, io.req.valid)
    when _T_682 : 
{
      node _T_684 = eq(cmdMul, UInt<1>(0))
      node _T_685 = and(rhs_sign, _T_684)
      node _T_686 = or(lhs_sign, _T_685)
      node _T_687 = mux(_T_686, UInt<3>(1), UInt<3>(2))
      state <= _T_687
      isMul <= cmdMul
      isHi <= cmdHi
      count <= UInt<1>(0)
      node _T_690 = eq(cmdMul, UInt<1>(0))
      node _T_691 = neq(lhs_sign, rhs_sign)
      node _T_692 = mux(cmdHi, lhs_sign, _T_691)
      node _T_693 = and(_T_690, _T_692)
      neg_out <= _T_693
      node _T_694 = cat(rhs_sign, rhs_in)
      divisor <= _T_694
      remainder <= lhs_in
      req <= io.req.bits_wky
      skip
}
    io.resp.bits_wky <= req
    node _T_697 = eq(req.dw, UInt<1>(0))
    node _T_698 = and(UInt<1>(1), _T_697)
    node _T_699 = bits(remainder, 31, 31)
    node _T_700 = bits(_T_699, 0, 0)
    node _T_703 = mux(_T_700, UInt<32>(4294967295), UInt<32>(0))
    node _T_704 = bits(remainder, 31, 0)
    node _T_705 = cat(_T_703, _T_704)
    node _T_706 = bits(remainder, 63, 0)
    node _T_707 = mux(_T_698, _T_705, _T_706)
    io.resp.bits_wky.data <= _T_707
    node _T_708 = eq(state, UInt<3>(5))
    io.resp.valid <= _T_708
    node _T_709 = eq(state, UInt<3>(0))
    io.req.ready <= _T_709
  module RVCExpander : 
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip in : UInt<32>, out : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}, rvc : UInt<1>}
    io is invalid
    io is invalid
    node _T_12 = bits(io.in, 1, 0)
    node _T_14 = neq(_T_12, UInt<2>(3))
    io.rvc <= _T_14
    node _T_15 = bits(io.in, 12, 5)
    node _T_17 = neq(_T_15, UInt<1>(0))
    node _T_20 = mux(_T_17, UInt<7>(19), UInt<7>(31))
    node _T_21 = bits(io.in, 10, 7)
    node _T_22 = bits(io.in, 12, 11)
    node _T_23 = bits(io.in, 5, 5)
    node _T_24 = bits(io.in, 6, 6)
    node _T_26 = cat(_T_24, UInt<2>(0))
    node _T_27 = cat(_T_21, _T_22)
    node _T_28 = cat(_T_27, _T_23)
    node _T_29 = cat(_T_28, _T_26)
    node _T_33 = bits(io.in, 4, 2)
    node _T_34 = cat(UInt<2>(1), _T_33)
    node _T_35 = cat(_T_34, _T_20)
    node _T_36 = cat(_T_29, UInt<5>(2))
    node _T_37 = cat(_T_36, UInt<3>(0))
    node _T_38 = cat(_T_37, _T_35)
    node _T_40 = bits(io.in, 4, 2)
    node _T_41 = cat(UInt<2>(1), _T_40)
    node _T_44 = bits(io.in, 4, 2)
    node _T_45 = cat(UInt<2>(1), _T_44)
    node _T_46 = bits(io.in, 31, 27)
    wire _T_53 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_53 is invalid
    _T_53.bits_wky <= _T_38
    _T_53.rd <= _T_41
    _T_53.rs1 <= UInt<5>(2)
    _T_53.rs2 <= _T_45
    _T_53.rs3 <= _T_46
    node _T_59 = bits(io.in, 6, 5)
    node _T_60 = bits(io.in, 12, 10)
    node _T_62 = cat(_T_59, _T_60)
    node _T_63 = cat(_T_62, UInt<3>(0))
    node _T_65 = bits(io.in, 9, 7)
    node _T_66 = cat(UInt<2>(1), _T_65)
    node _T_69 = bits(io.in, 4, 2)
    node _T_70 = cat(UInt<2>(1), _T_69)
    node _T_72 = cat(_T_70, UInt<7>(7))
    node _T_73 = cat(_T_63, _T_66)
    node _T_74 = cat(_T_73, UInt<3>(3))
    node _T_75 = cat(_T_74, _T_72)
    node _T_77 = bits(io.in, 4, 2)
    node _T_78 = cat(UInt<2>(1), _T_77)
    node _T_80 = bits(io.in, 9, 7)
    node _T_81 = cat(UInt<2>(1), _T_80)
    node _T_83 = bits(io.in, 4, 2)
    node _T_84 = cat(UInt<2>(1), _T_83)
    node _T_85 = bits(io.in, 31, 27)
    wire _T_92 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_92 is invalid
    _T_92.bits_wky <= _T_75
    _T_92.rd <= _T_78
    _T_92.rs1 <= _T_81
    _T_92.rs2 <= _T_84
    _T_92.rs3 <= _T_85
    node _T_98 = bits(io.in, 5, 5)
    node _T_99 = bits(io.in, 12, 10)
    node _T_100 = bits(io.in, 6, 6)
    node _T_102 = cat(_T_100, UInt<2>(0))
    node _T_103 = cat(_T_98, _T_99)
    node _T_104 = cat(_T_103, _T_102)
    node _T_106 = bits(io.in, 9, 7)
    node _T_107 = cat(UInt<2>(1), _T_106)
    node _T_110 = bits(io.in, 4, 2)
    node _T_111 = cat(UInt<2>(1), _T_110)
    node _T_113 = cat(_T_111, UInt<7>(3))
    node _T_114 = cat(_T_104, _T_107)
    node _T_115 = cat(_T_114, UInt<3>(2))
    node _T_116 = cat(_T_115, _T_113)
    node _T_118 = bits(io.in, 4, 2)
    node _T_119 = cat(UInt<2>(1), _T_118)
    node _T_121 = bits(io.in, 9, 7)
    node _T_122 = cat(UInt<2>(1), _T_121)
    node _T_124 = bits(io.in, 4, 2)
    node _T_125 = cat(UInt<2>(1), _T_124)
    node _T_126 = bits(io.in, 31, 27)
    wire _T_133 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_133 is invalid
    _T_133.bits_wky <= _T_116
    _T_133.rd <= _T_119
    _T_133.rs1 <= _T_122
    _T_133.rs2 <= _T_125
    _T_133.rs3 <= _T_126
    node _T_139 = bits(io.in, 6, 5)
    node _T_140 = bits(io.in, 12, 10)
    node _T_142 = cat(_T_139, _T_140)
    node _T_143 = cat(_T_142, UInt<3>(0))
    node _T_145 = bits(io.in, 9, 7)
    node _T_146 = cat(UInt<2>(1), _T_145)
    node _T_149 = bits(io.in, 4, 2)
    node _T_150 = cat(UInt<2>(1), _T_149)
    node _T_152 = cat(_T_150, UInt<7>(3))
    node _T_153 = cat(_T_143, _T_146)
    node _T_154 = cat(_T_153, UInt<3>(3))
    node _T_155 = cat(_T_154, _T_152)
    node _T_157 = bits(io.in, 4, 2)
    node _T_158 = cat(UInt<2>(1), _T_157)
    node _T_160 = bits(io.in, 9, 7)
    node _T_161 = cat(UInt<2>(1), _T_160)
    node _T_163 = bits(io.in, 4, 2)
    node _T_164 = cat(UInt<2>(1), _T_163)
    node _T_165 = bits(io.in, 31, 27)
    wire _T_172 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_172 is invalid
    _T_172.bits_wky <= _T_155
    _T_172.rd <= _T_158
    _T_172.rs1 <= _T_161
    _T_172.rs2 <= _T_164
    _T_172.rs3 <= _T_165
    node _T_178 = bits(io.in, 5, 5)
    node _T_179 = bits(io.in, 12, 10)
    node _T_180 = bits(io.in, 6, 6)
    node _T_182 = cat(_T_180, UInt<2>(0))
    node _T_183 = cat(_T_178, _T_179)
    node _T_184 = cat(_T_183, _T_182)
    node _T_185 = shr(_T_184, 5)
    node _T_187 = bits(io.in, 4, 2)
    node _T_188 = cat(UInt<2>(1), _T_187)
    node _T_190 = bits(io.in, 9, 7)
    node _T_191 = cat(UInt<2>(1), _T_190)
    node _T_193 = bits(io.in, 5, 5)
    node _T_194 = bits(io.in, 12, 10)
    node _T_195 = bits(io.in, 6, 6)
    node _T_197 = cat(_T_195, UInt<2>(0))
    node _T_198 = cat(_T_193, _T_194)
    node _T_199 = cat(_T_198, _T_197)
    node _T_200 = bits(_T_199, 4, 0)
    node _T_202 = cat(UInt<3>(2), _T_200)
    node _T_203 = cat(_T_202, UInt<7>(47))
    node _T_204 = cat(_T_185, _T_188)
    node _T_205 = cat(_T_204, _T_191)
    node _T_206 = cat(_T_205, _T_203)
    node _T_208 = bits(io.in, 4, 2)
    node _T_209 = cat(UInt<2>(1), _T_208)
    node _T_211 = bits(io.in, 9, 7)
    node _T_212 = cat(UInt<2>(1), _T_211)
    node _T_214 = bits(io.in, 4, 2)
    node _T_215 = cat(UInt<2>(1), _T_214)
    node _T_216 = bits(io.in, 31, 27)
    wire _T_223 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_223 is invalid
    _T_223.bits_wky <= _T_206
    _T_223.rd <= _T_209
    _T_223.rs1 <= _T_212
    _T_223.rs2 <= _T_215
    _T_223.rs3 <= _T_216
    node _T_229 = bits(io.in, 6, 5)
    node _T_230 = bits(io.in, 12, 10)
    node _T_232 = cat(_T_229, _T_230)
    node _T_233 = cat(_T_232, UInt<3>(0))
    node _T_234 = shr(_T_233, 5)
    node _T_236 = bits(io.in, 4, 2)
    node _T_237 = cat(UInt<2>(1), _T_236)
    node _T_239 = bits(io.in, 9, 7)
    node _T_240 = cat(UInt<2>(1), _T_239)
    node _T_242 = bits(io.in, 6, 5)
    node _T_243 = bits(io.in, 12, 10)
    node _T_245 = cat(_T_242, _T_243)
    node _T_246 = cat(_T_245, UInt<3>(0))
    node _T_247 = bits(_T_246, 4, 0)
    node _T_249 = cat(UInt<3>(3), _T_247)
    node _T_250 = cat(_T_249, UInt<7>(39))
    node _T_251 = cat(_T_234, _T_237)
    node _T_252 = cat(_T_251, _T_240)
    node _T_253 = cat(_T_252, _T_250)
    node _T_255 = bits(io.in, 4, 2)
    node _T_256 = cat(UInt<2>(1), _T_255)
    node _T_258 = bits(io.in, 9, 7)
    node _T_259 = cat(UInt<2>(1), _T_258)
    node _T_261 = bits(io.in, 4, 2)
    node _T_262 = cat(UInt<2>(1), _T_261)
    node _T_263 = bits(io.in, 31, 27)
    wire _T_270 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_270 is invalid
    _T_270.bits_wky <= _T_253
    _T_270.rd <= _T_256
    _T_270.rs1 <= _T_259
    _T_270.rs2 <= _T_262
    _T_270.rs3 <= _T_263
    node _T_276 = bits(io.in, 5, 5)
    node _T_277 = bits(io.in, 12, 10)
    node _T_278 = bits(io.in, 6, 6)
    node _T_280 = cat(_T_278, UInt<2>(0))
    node _T_281 = cat(_T_276, _T_277)
    node _T_282 = cat(_T_281, _T_280)
    node _T_283 = shr(_T_282, 5)
    node _T_285 = bits(io.in, 4, 2)
    node _T_286 = cat(UInt<2>(1), _T_285)
    node _T_288 = bits(io.in, 9, 7)
    node _T_289 = cat(UInt<2>(1), _T_288)
    node _T_291 = bits(io.in, 5, 5)
    node _T_292 = bits(io.in, 12, 10)
    node _T_293 = bits(io.in, 6, 6)
    node _T_295 = cat(_T_293, UInt<2>(0))
    node _T_296 = cat(_T_291, _T_292)
    node _T_297 = cat(_T_296, _T_295)
    node _T_298 = bits(_T_297, 4, 0)
    node _T_300 = cat(UInt<3>(2), _T_298)
    node _T_301 = cat(_T_300, UInt<7>(35))
    node _T_302 = cat(_T_283, _T_286)
    node _T_303 = cat(_T_302, _T_289)
    node _T_304 = cat(_T_303, _T_301)
    node _T_306 = bits(io.in, 4, 2)
    node _T_307 = cat(UInt<2>(1), _T_306)
    node _T_309 = bits(io.in, 9, 7)
    node _T_310 = cat(UInt<2>(1), _T_309)
    node _T_312 = bits(io.in, 4, 2)
    node _T_313 = cat(UInt<2>(1), _T_312)
    node _T_314 = bits(io.in, 31, 27)
    wire _T_321 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_321 is invalid
    _T_321.bits_wky <= _T_304
    _T_321.rd <= _T_307
    _T_321.rs1 <= _T_310
    _T_321.rs2 <= _T_313
    _T_321.rs3 <= _T_314
    node _T_327 = bits(io.in, 6, 5)
    node _T_328 = bits(io.in, 12, 10)
    node _T_330 = cat(_T_327, _T_328)
    node _T_331 = cat(_T_330, UInt<3>(0))
    node _T_332 = shr(_T_331, 5)
    node _T_334 = bits(io.in, 4, 2)
    node _T_335 = cat(UInt<2>(1), _T_334)
    node _T_337 = bits(io.in, 9, 7)
    node _T_338 = cat(UInt<2>(1), _T_337)
    node _T_340 = bits(io.in, 6, 5)
    node _T_341 = bits(io.in, 12, 10)
    node _T_343 = cat(_T_340, _T_341)
    node _T_344 = cat(_T_343, UInt<3>(0))
    node _T_345 = bits(_T_344, 4, 0)
    node _T_347 = cat(UInt<3>(3), _T_345)
    node _T_348 = cat(_T_347, UInt<7>(35))
    node _T_349 = cat(_T_332, _T_335)
    node _T_350 = cat(_T_349, _T_338)
    node _T_351 = cat(_T_350, _T_348)
    node _T_353 = bits(io.in, 4, 2)
    node _T_354 = cat(UInt<2>(1), _T_353)
    node _T_356 = bits(io.in, 9, 7)
    node _T_357 = cat(UInt<2>(1), _T_356)
    node _T_359 = bits(io.in, 4, 2)
    node _T_360 = cat(UInt<2>(1), _T_359)
    node _T_361 = bits(io.in, 31, 27)
    wire _T_368 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_368 is invalid
    _T_368.bits_wky <= _T_351
    _T_368.rd <= _T_354
    _T_368.rs1 <= _T_357
    _T_368.rs2 <= _T_360
    _T_368.rs3 <= _T_361
    node _T_374 = bits(io.in, 12, 12)
    node _T_375 = bits(_T_374, 0, 0)
    node _T_378 = mux(_T_375, UInt<7>(127), UInt<7>(0))
    node _T_379 = bits(io.in, 6, 2)
    node _T_380 = cat(_T_378, _T_379)
    node _T_381 = bits(io.in, 11, 7)
    node _T_383 = bits(io.in, 11, 7)
    node _T_385 = cat(_T_383, UInt<7>(19))
    node _T_386 = cat(_T_380, _T_381)
    node _T_387 = cat(_T_386, UInt<3>(0))
    node _T_388 = cat(_T_387, _T_385)
    node _T_389 = bits(io.in, 11, 7)
    node _T_390 = bits(io.in, 11, 7)
    node _T_392 = bits(io.in, 4, 2)
    node _T_393 = cat(UInt<2>(1), _T_392)
    node _T_394 = bits(io.in, 31, 27)
    wire _T_401 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_401 is invalid
    _T_401.bits_wky <= _T_388
    _T_401.rd <= _T_389
    _T_401.rs1 <= _T_390
    _T_401.rs2 <= _T_393
    _T_401.rs3 <= _T_394
    node _T_407 = bits(io.in, 11, 7)
    node _T_409 = neq(_T_407, UInt<1>(0))
    node _T_412 = mux(_T_409, UInt<7>(27), UInt<7>(31))
    node _T_413 = bits(io.in, 12, 12)
    node _T_414 = bits(_T_413, 0, 0)
    node _T_417 = mux(_T_414, UInt<7>(127), UInt<7>(0))
    node _T_418 = bits(io.in, 6, 2)
    node _T_419 = cat(_T_417, _T_418)
    node _T_420 = bits(io.in, 11, 7)
    node _T_422 = bits(io.in, 11, 7)
    node _T_423 = cat(_T_422, _T_412)
    node _T_424 = cat(_T_419, _T_420)
    node _T_425 = cat(_T_424, UInt<3>(0))
    node _T_426 = cat(_T_425, _T_423)
    node _T_427 = bits(io.in, 11, 7)
    node _T_428 = bits(io.in, 11, 7)
    node _T_430 = bits(io.in, 4, 2)
    node _T_431 = cat(UInt<2>(1), _T_430)
    node _T_432 = bits(io.in, 31, 27)
    wire _T_439 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_439 is invalid
    _T_439.bits_wky <= _T_426
    _T_439.rd <= _T_427
    _T_439.rs1 <= _T_428
    _T_439.rs2 <= _T_431
    _T_439.rs3 <= _T_432
    node _T_445 = bits(io.in, 12, 12)
    node _T_446 = bits(_T_445, 0, 0)
    node _T_449 = mux(_T_446, UInt<7>(127), UInt<7>(0))
    node _T_450 = bits(io.in, 6, 2)
    node _T_451 = cat(_T_449, _T_450)
    node _T_454 = bits(io.in, 11, 7)
    node _T_456 = cat(_T_454, UInt<7>(19))
    node _T_457 = cat(_T_451, UInt<5>(0))
    node _T_458 = cat(_T_457, UInt<3>(0))
    node _T_459 = cat(_T_458, _T_456)
    node _T_460 = bits(io.in, 11, 7)
    node _T_463 = bits(io.in, 4, 2)
    node _T_464 = cat(UInt<2>(1), _T_463)
    node _T_465 = bits(io.in, 31, 27)
    wire _T_472 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_472 is invalid
    _T_472.bits_wky <= _T_459
    _T_472.rd <= _T_460
    _T_472.rs1 <= UInt<5>(0)
    _T_472.rs2 <= _T_464
    _T_472.rs3 <= _T_465
    node _T_478 = bits(io.in, 12, 12)
    node _T_479 = bits(_T_478, 0, 0)
    node _T_482 = mux(_T_479, UInt<7>(127), UInt<7>(0))
    node _T_483 = bits(io.in, 6, 2)
    node _T_484 = cat(_T_482, _T_483)
    node _T_486 = neq(_T_484, UInt<1>(0))
    node _T_489 = mux(_T_486, UInt<7>(55), UInt<7>(63))
    node _T_490 = bits(io.in, 12, 12)
    node _T_491 = bits(_T_490, 0, 0)
    node _T_494 = mux(_T_491, UInt<15>(32767), UInt<15>(0))
    node _T_495 = bits(io.in, 6, 2)
    node _T_497 = cat(_T_494, _T_495)
    node _T_498 = cat(_T_497, UInt<12>(0))
    node _T_499 = bits(_T_498, 31, 12)
    node _T_500 = bits(io.in, 11, 7)
    node _T_501 = cat(_T_499, _T_500)
    node _T_502 = cat(_T_501, _T_489)
    node _T_503 = bits(io.in, 11, 7)
    node _T_504 = bits(io.in, 11, 7)
    node _T_506 = bits(io.in, 4, 2)
    node _T_507 = cat(UInt<2>(1), _T_506)
    node _T_508 = bits(io.in, 31, 27)
    wire _T_515 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_515 is invalid
    _T_515.bits_wky <= _T_502
    _T_515.rd <= _T_503
    _T_515.rs1 <= _T_504
    _T_515.rs2 <= _T_507
    _T_515.rs3 <= _T_508
    node _T_521 = bits(io.in, 11, 7)
    node _T_523 = eq(_T_521, UInt<5>(0))
    node _T_524 = bits(io.in, 11, 7)
    node _T_526 = eq(_T_524, UInt<5>(2))
    node _T_527 = or(_T_523, _T_526)
    node _T_528 = bits(io.in, 12, 12)
    node _T_529 = bits(_T_528, 0, 0)
    node _T_532 = mux(_T_529, UInt<7>(127), UInt<7>(0))
    node _T_533 = bits(io.in, 6, 2)
    node _T_534 = cat(_T_532, _T_533)
    node _T_536 = neq(_T_534, UInt<1>(0))
    node _T_539 = mux(_T_536, UInt<7>(19), UInt<7>(31))
    node _T_540 = bits(io.in, 12, 12)
    node _T_541 = bits(_T_540, 0, 0)
    node _T_544 = mux(_T_541, UInt<3>(7), UInt<3>(0))
    node _T_545 = bits(io.in, 4, 3)
    node _T_546 = bits(io.in, 5, 5)
    node _T_547 = bits(io.in, 2, 2)
    node _T_548 = bits(io.in, 6, 6)
    node _T_550 = cat(_T_547, _T_548)
    node _T_551 = cat(_T_550, UInt<4>(0))
    node _T_552 = cat(_T_544, _T_545)
    node _T_553 = cat(_T_552, _T_546)
    node _T_554 = cat(_T_553, _T_551)
    node _T_555 = bits(io.in, 11, 7)
    node _T_557 = bits(io.in, 11, 7)
    node _T_558 = cat(_T_557, _T_539)
    node _T_559 = cat(_T_554, _T_555)
    node _T_560 = cat(_T_559, UInt<3>(0))
    node _T_561 = cat(_T_560, _T_558)
    node _T_562 = bits(io.in, 11, 7)
    node _T_563 = bits(io.in, 11, 7)
    node _T_565 = bits(io.in, 4, 2)
    node _T_566 = cat(UInt<2>(1), _T_565)
    node _T_567 = bits(io.in, 31, 27)
    wire _T_574 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_574 is invalid
    _T_574.bits_wky <= _T_561
    _T_574.rd <= _T_562
    _T_574.rs1 <= _T_563
    _T_574.rs2 <= _T_566
    _T_574.rs3 <= _T_567
    node _T_580 = mux(_T_527, _T_574, _T_515)
    node _T_586 = bits(io.in, 12, 12)
    node _T_587 = bits(io.in, 6, 2)
    node _T_588 = cat(_T_586, _T_587)
    node _T_590 = bits(io.in, 9, 7)
    node _T_591 = cat(UInt<2>(1), _T_590)
    node _T_594 = bits(io.in, 9, 7)
    node _T_595 = cat(UInt<2>(1), _T_594)
    node _T_597 = cat(_T_595, UInt<7>(19))
    node _T_598 = cat(_T_588, _T_591)
    node _T_599 = cat(_T_598, UInt<3>(5))
    node _T_600 = cat(_T_599, _T_597)
    node _T_601 = bits(io.in, 12, 12)
    node _T_602 = bits(io.in, 6, 2)
    node _T_603 = cat(_T_601, _T_602)
    node _T_605 = bits(io.in, 9, 7)
    node _T_606 = cat(UInt<2>(1), _T_605)
    node _T_609 = bits(io.in, 9, 7)
    node _T_610 = cat(UInt<2>(1), _T_609)
    node _T_612 = cat(_T_610, UInt<7>(19))
    node _T_613 = cat(_T_603, _T_606)
    node _T_614 = cat(_T_613, UInt<3>(5))
    node _T_615 = cat(_T_614, _T_612)
    node _T_617 = or(_T_615, UInt<31>(1073741824))
    node _T_618 = bits(io.in, 12, 12)
    node _T_619 = bits(_T_618, 0, 0)
    node _T_622 = mux(_T_619, UInt<7>(127), UInt<7>(0))
    node _T_623 = bits(io.in, 6, 2)
    node _T_624 = cat(_T_622, _T_623)
    node _T_626 = bits(io.in, 9, 7)
    node _T_627 = cat(UInt<2>(1), _T_626)
    node _T_630 = bits(io.in, 9, 7)
    node _T_631 = cat(UInt<2>(1), _T_630)
    node _T_633 = cat(_T_631, UInt<7>(19))
    node _T_634 = cat(_T_624, _T_627)
    node _T_635 = cat(_T_634, UInt<3>(7))
    node _T_636 = cat(_T_635, _T_633)
    node _T_645 = bits(io.in, 12, 12)
    node _T_646 = bits(io.in, 6, 5)
    node _T_647 = cat(_T_645, _T_646)
    node _T_649 = and(_T_647, UInt<2>(3))
    node _T_651 = geq(_T_647, UInt<3>(4))
    node _T_653 = and(_T_649, UInt<1>(1))
    node _T_655 = geq(_T_649, UInt<2>(2))
    node _T_657 = and(_T_653, UInt<1>(0))
    node _T_659 = geq(_T_653, UInt<1>(1))
    node _T_660 = mux(_T_659, UInt<2>(3), UInt<2>(2))
    node _T_662 = and(_T_653, UInt<1>(0))
    node _T_664 = geq(_T_653, UInt<1>(1))
    node _T_665 = mux(_T_664, UInt<1>(0), UInt<1>(0))
    node _T_666 = mux(_T_655, _T_660, _T_665)
    node _T_668 = and(_T_649, UInt<1>(1))
    node _T_670 = geq(_T_649, UInt<2>(2))
    node _T_672 = and(_T_668, UInt<1>(0))
    node _T_674 = geq(_T_668, UInt<1>(1))
    node _T_675 = mux(_T_674, UInt<3>(7), UInt<3>(6))
    node _T_677 = and(_T_668, UInt<1>(0))
    node _T_679 = geq(_T_668, UInt<1>(1))
    node _T_680 = mux(_T_679, UInt<3>(4), UInt<1>(0))
    node _T_681 = mux(_T_670, _T_675, _T_680)
    node _T_682 = mux(_T_651, _T_666, _T_681)
    node _T_683 = bits(io.in, 6, 5)
    node _T_685 = eq(_T_683, UInt<1>(0))
    node _T_688 = mux(_T_685, UInt<31>(1073741824), UInt<1>(0))
    node _T_689 = bits(io.in, 12, 12)
    node _T_692 = mux(_T_689, UInt<7>(59), UInt<7>(51))
    node _T_694 = bits(io.in, 4, 2)
    node _T_695 = cat(UInt<2>(1), _T_694)
    node _T_697 = bits(io.in, 9, 7)
    node _T_698 = cat(UInt<2>(1), _T_697)
    node _T_700 = bits(io.in, 9, 7)
    node _T_701 = cat(UInt<2>(1), _T_700)
    node _T_702 = cat(_T_701, _T_692)
    node _T_703 = cat(_T_695, _T_698)
    node _T_704 = cat(_T_703, _T_682)
    node _T_705 = cat(_T_704, _T_702)
    node _T_706 = or(_T_705, _T_688)
    node _T_707 = bits(io.in, 11, 10)
    node _T_709 = and(_T_707, UInt<1>(1))
    node _T_711 = geq(_T_707, UInt<2>(2))
    node _T_713 = and(_T_709, UInt<1>(0))
    node _T_715 = geq(_T_709, UInt<1>(1))
    node _T_716 = mux(_T_715, _T_706, _T_636)
    node _T_718 = and(_T_709, UInt<1>(0))
    node _T_720 = geq(_T_709, UInt<1>(1))
    node _T_721 = mux(_T_720, _T_617, _T_600)
    node _T_722 = mux(_T_711, _T_716, _T_721)
    node _T_724 = bits(io.in, 9, 7)
    node _T_725 = cat(UInt<2>(1), _T_724)
    node _T_727 = bits(io.in, 9, 7)
    node _T_728 = cat(UInt<2>(1), _T_727)
    node _T_730 = bits(io.in, 4, 2)
    node _T_731 = cat(UInt<2>(1), _T_730)
    node _T_732 = bits(io.in, 31, 27)
    wire _T_739 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_739 is invalid
    _T_739.bits_wky <= _T_722
    _T_739.rd <= _T_725
    _T_739.rs1 <= _T_728
    _T_739.rs2 <= _T_731
    _T_739.rs3 <= _T_732
    node _T_745 = bits(io.in, 12, 12)
    node _T_746 = bits(_T_745, 0, 0)
    node _T_749 = mux(_T_746, UInt<10>(1023), UInt<10>(0))
    node _T_750 = bits(io.in, 8, 8)
    node _T_751 = bits(io.in, 10, 9)
    node _T_752 = bits(io.in, 6, 6)
    node _T_753 = bits(io.in, 7, 7)
    node _T_754 = bits(io.in, 2, 2)
    node _T_755 = bits(io.in, 11, 11)
    node _T_756 = bits(io.in, 5, 3)
    node _T_758 = cat(_T_756, UInt<1>(0))
    node _T_759 = cat(_T_754, _T_755)
    node _T_760 = cat(_T_759, _T_758)
    node _T_761 = cat(_T_752, _T_753)
    node _T_762 = cat(_T_749, _T_750)
    node _T_763 = cat(_T_762, _T_751)
    node _T_764 = cat(_T_763, _T_761)
    node _T_765 = cat(_T_764, _T_760)
    node _T_766 = bits(_T_765, 20, 20)
    node _T_767 = bits(io.in, 12, 12)
    node _T_768 = bits(_T_767, 0, 0)
    node _T_771 = mux(_T_768, UInt<10>(1023), UInt<10>(0))
    node _T_772 = bits(io.in, 8, 8)
    node _T_773 = bits(io.in, 10, 9)
    node _T_774 = bits(io.in, 6, 6)
    node _T_775 = bits(io.in, 7, 7)
    node _T_776 = bits(io.in, 2, 2)
    node _T_777 = bits(io.in, 11, 11)
    node _T_778 = bits(io.in, 5, 3)
    node _T_780 = cat(_T_778, UInt<1>(0))
    node _T_781 = cat(_T_776, _T_777)
    node _T_782 = cat(_T_781, _T_780)
    node _T_783 = cat(_T_774, _T_775)
    node _T_784 = cat(_T_771, _T_772)
    node _T_785 = cat(_T_784, _T_773)
    node _T_786 = cat(_T_785, _T_783)
    node _T_787 = cat(_T_786, _T_782)
    node _T_788 = bits(_T_787, 10, 1)
    node _T_789 = bits(io.in, 12, 12)
    node _T_790 = bits(_T_789, 0, 0)
    node _T_793 = mux(_T_790, UInt<10>(1023), UInt<10>(0))
    node _T_794 = bits(io.in, 8, 8)
    node _T_795 = bits(io.in, 10, 9)
    node _T_796 = bits(io.in, 6, 6)
    node _T_797 = bits(io.in, 7, 7)
    node _T_798 = bits(io.in, 2, 2)
    node _T_799 = bits(io.in, 11, 11)
    node _T_800 = bits(io.in, 5, 3)
    node _T_802 = cat(_T_800, UInt<1>(0))
    node _T_803 = cat(_T_798, _T_799)
    node _T_804 = cat(_T_803, _T_802)
    node _T_805 = cat(_T_796, _T_797)
    node _T_806 = cat(_T_793, _T_794)
    node _T_807 = cat(_T_806, _T_795)
    node _T_808 = cat(_T_807, _T_805)
    node _T_809 = cat(_T_808, _T_804)
    node _T_810 = bits(_T_809, 11, 11)
    node _T_811 = bits(io.in, 12, 12)
    node _T_812 = bits(_T_811, 0, 0)
    node _T_815 = mux(_T_812, UInt<10>(1023), UInt<10>(0))
    node _T_816 = bits(io.in, 8, 8)
    node _T_817 = bits(io.in, 10, 9)
    node _T_818 = bits(io.in, 6, 6)
    node _T_819 = bits(io.in, 7, 7)
    node _T_820 = bits(io.in, 2, 2)
    node _T_821 = bits(io.in, 11, 11)
    node _T_822 = bits(io.in, 5, 3)
    node _T_824 = cat(_T_822, UInt<1>(0))
    node _T_825 = cat(_T_820, _T_821)
    node _T_826 = cat(_T_825, _T_824)
    node _T_827 = cat(_T_818, _T_819)
    node _T_828 = cat(_T_815, _T_816)
    node _T_829 = cat(_T_828, _T_817)
    node _T_830 = cat(_T_829, _T_827)
    node _T_831 = cat(_T_830, _T_826)
    node _T_832 = bits(_T_831, 19, 12)
    node _T_835 = cat(_T_832, UInt<5>(0))
    node _T_836 = cat(_T_835, UInt<7>(111))
    node _T_837 = cat(_T_766, _T_788)
    node _T_838 = cat(_T_837, _T_810)
    node _T_839 = cat(_T_838, _T_836)
    node _T_842 = bits(io.in, 9, 7)
    node _T_843 = cat(UInt<2>(1), _T_842)
    node _T_845 = bits(io.in, 4, 2)
    node _T_846 = cat(UInt<2>(1), _T_845)
    node _T_847 = bits(io.in, 31, 27)
    wire _T_854 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_854 is invalid
    _T_854.bits_wky <= _T_839
    _T_854.rd <= UInt<5>(0)
    _T_854.rs1 <= _T_843
    _T_854.rs2 <= _T_846
    _T_854.rs3 <= _T_847
    node _T_860 = bits(io.in, 12, 12)
    node _T_861 = bits(_T_860, 0, 0)
    node _T_864 = mux(_T_861, UInt<5>(31), UInt<5>(0))
    node _T_865 = bits(io.in, 6, 5)
    node _T_866 = bits(io.in, 2, 2)
    node _T_867 = bits(io.in, 11, 10)
    node _T_868 = bits(io.in, 4, 3)
    node _T_870 = cat(_T_867, _T_868)
    node _T_871 = cat(_T_870, UInt<1>(0))
    node _T_872 = cat(_T_864, _T_865)
    node _T_873 = cat(_T_872, _T_866)
    node _T_874 = cat(_T_873, _T_871)
    node _T_875 = bits(_T_874, 12, 12)
    node _T_876 = bits(io.in, 12, 12)
    node _T_877 = bits(_T_876, 0, 0)
    node _T_880 = mux(_T_877, UInt<5>(31), UInt<5>(0))
    node _T_881 = bits(io.in, 6, 5)
    node _T_882 = bits(io.in, 2, 2)
    node _T_883 = bits(io.in, 11, 10)
    node _T_884 = bits(io.in, 4, 3)
    node _T_886 = cat(_T_883, _T_884)
    node _T_887 = cat(_T_886, UInt<1>(0))
    node _T_888 = cat(_T_880, _T_881)
    node _T_889 = cat(_T_888, _T_882)
    node _T_890 = cat(_T_889, _T_887)
    node _T_891 = bits(_T_890, 10, 5)
    node _T_894 = bits(io.in, 9, 7)
    node _T_895 = cat(UInt<2>(1), _T_894)
    node _T_897 = bits(io.in, 12, 12)
    node _T_898 = bits(_T_897, 0, 0)
    node _T_901 = mux(_T_898, UInt<5>(31), UInt<5>(0))
    node _T_902 = bits(io.in, 6, 5)
    node _T_903 = bits(io.in, 2, 2)
    node _T_904 = bits(io.in, 11, 10)
    node _T_905 = bits(io.in, 4, 3)
    node _T_907 = cat(_T_904, _T_905)
    node _T_908 = cat(_T_907, UInt<1>(0))
    node _T_909 = cat(_T_901, _T_902)
    node _T_910 = cat(_T_909, _T_903)
    node _T_911 = cat(_T_910, _T_908)
    node _T_912 = bits(_T_911, 4, 1)
    node _T_913 = bits(io.in, 12, 12)
    node _T_914 = bits(_T_913, 0, 0)
    node _T_917 = mux(_T_914, UInt<5>(31), UInt<5>(0))
    node _T_918 = bits(io.in, 6, 5)
    node _T_919 = bits(io.in, 2, 2)
    node _T_920 = bits(io.in, 11, 10)
    node _T_921 = bits(io.in, 4, 3)
    node _T_923 = cat(_T_920, _T_921)
    node _T_924 = cat(_T_923, UInt<1>(0))
    node _T_925 = cat(_T_917, _T_918)
    node _T_926 = cat(_T_925, _T_919)
    node _T_927 = cat(_T_926, _T_924)
    node _T_928 = bits(_T_927, 11, 11)
    node _T_930 = cat(_T_928, UInt<7>(99))
    node _T_931 = cat(UInt<3>(0), _T_912)
    node _T_932 = cat(_T_931, _T_930)
    node _T_933 = cat(UInt<5>(0), _T_895)
    node _T_934 = cat(_T_875, _T_891)
    node _T_935 = cat(_T_934, _T_933)
    node _T_936 = cat(_T_935, _T_932)
    node _T_938 = bits(io.in, 9, 7)
    node _T_939 = cat(UInt<2>(1), _T_938)
    node _T_941 = bits(io.in, 9, 7)
    node _T_942 = cat(UInt<2>(1), _T_941)
    node _T_944 = bits(io.in, 31, 27)
    wire _T_951 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_951 is invalid
    _T_951.bits_wky <= _T_936
    _T_951.rd <= _T_939
    _T_951.rs1 <= _T_942
    _T_951.rs2 <= UInt<5>(0)
    _T_951.rs3 <= _T_944
    node _T_957 = bits(io.in, 12, 12)
    node _T_958 = bits(_T_957, 0, 0)
    node _T_961 = mux(_T_958, UInt<5>(31), UInt<5>(0))
    node _T_962 = bits(io.in, 6, 5)
    node _T_963 = bits(io.in, 2, 2)
    node _T_964 = bits(io.in, 11, 10)
    node _T_965 = bits(io.in, 4, 3)
    node _T_967 = cat(_T_964, _T_965)
    node _T_968 = cat(_T_967, UInt<1>(0))
    node _T_969 = cat(_T_961, _T_962)
    node _T_970 = cat(_T_969, _T_963)
    node _T_971 = cat(_T_970, _T_968)
    node _T_972 = bits(_T_971, 12, 12)
    node _T_973 = bits(io.in, 12, 12)
    node _T_974 = bits(_T_973, 0, 0)
    node _T_977 = mux(_T_974, UInt<5>(31), UInt<5>(0))
    node _T_978 = bits(io.in, 6, 5)
    node _T_979 = bits(io.in, 2, 2)
    node _T_980 = bits(io.in, 11, 10)
    node _T_981 = bits(io.in, 4, 3)
    node _T_983 = cat(_T_980, _T_981)
    node _T_984 = cat(_T_983, UInt<1>(0))
    node _T_985 = cat(_T_977, _T_978)
    node _T_986 = cat(_T_985, _T_979)
    node _T_987 = cat(_T_986, _T_984)
    node _T_988 = bits(_T_987, 10, 5)
    node _T_991 = bits(io.in, 9, 7)
    node _T_992 = cat(UInt<2>(1), _T_991)
    node _T_994 = bits(io.in, 12, 12)
    node _T_995 = bits(_T_994, 0, 0)
    node _T_998 = mux(_T_995, UInt<5>(31), UInt<5>(0))
    node _T_999 = bits(io.in, 6, 5)
    node _T_1000 = bits(io.in, 2, 2)
    node _T_1001 = bits(io.in, 11, 10)
    node _T_1002 = bits(io.in, 4, 3)
    node _T_1004 = cat(_T_1001, _T_1002)
    node _T_1005 = cat(_T_1004, UInt<1>(0))
    node _T_1006 = cat(_T_998, _T_999)
    node _T_1007 = cat(_T_1006, _T_1000)
    node _T_1008 = cat(_T_1007, _T_1005)
    node _T_1009 = bits(_T_1008, 4, 1)
    node _T_1010 = bits(io.in, 12, 12)
    node _T_1011 = bits(_T_1010, 0, 0)
    node _T_1014 = mux(_T_1011, UInt<5>(31), UInt<5>(0))
    node _T_1015 = bits(io.in, 6, 5)
    node _T_1016 = bits(io.in, 2, 2)
    node _T_1017 = bits(io.in, 11, 10)
    node _T_1018 = bits(io.in, 4, 3)
    node _T_1020 = cat(_T_1017, _T_1018)
    node _T_1021 = cat(_T_1020, UInt<1>(0))
    node _T_1022 = cat(_T_1014, _T_1015)
    node _T_1023 = cat(_T_1022, _T_1016)
    node _T_1024 = cat(_T_1023, _T_1021)
    node _T_1025 = bits(_T_1024, 11, 11)
    node _T_1027 = cat(_T_1025, UInt<7>(99))
    node _T_1028 = cat(UInt<3>(1), _T_1009)
    node _T_1029 = cat(_T_1028, _T_1027)
    node _T_1030 = cat(UInt<5>(0), _T_992)
    node _T_1031 = cat(_T_972, _T_988)
    node _T_1032 = cat(_T_1031, _T_1030)
    node _T_1033 = cat(_T_1032, _T_1029)
    node _T_1036 = bits(io.in, 9, 7)
    node _T_1037 = cat(UInt<2>(1), _T_1036)
    node _T_1039 = bits(io.in, 31, 27)
    wire _T_1046 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1046 is invalid
    _T_1046.bits_wky <= _T_1033
    _T_1046.rd <= UInt<5>(0)
    _T_1046.rs1 <= _T_1037
    _T_1046.rs2 <= UInt<5>(0)
    _T_1046.rs3 <= _T_1039
    node _T_1052 = bits(io.in, 12, 12)
    node _T_1053 = bits(io.in, 6, 2)
    node _T_1054 = cat(_T_1052, _T_1053)
    node _T_1055 = bits(io.in, 11, 7)
    node _T_1057 = bits(io.in, 11, 7)
    node _T_1059 = cat(_T_1057, UInt<7>(19))
    node _T_1060 = cat(_T_1054, _T_1055)
    node _T_1061 = cat(_T_1060, UInt<3>(1))
    node _T_1062 = cat(_T_1061, _T_1059)
    node _T_1063 = bits(io.in, 11, 7)
    node _T_1064 = bits(io.in, 11, 7)
    node _T_1065 = bits(io.in, 6, 2)
    node _T_1066 = bits(io.in, 31, 27)
    wire _T_1073 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1073 is invalid
    _T_1073.bits_wky <= _T_1062
    _T_1073.rd <= _T_1063
    _T_1073.rs1 <= _T_1064
    _T_1073.rs2 <= _T_1065
    _T_1073.rs3 <= _T_1066
    node _T_1079 = bits(io.in, 4, 2)
    node _T_1080 = bits(io.in, 12, 12)
    node _T_1081 = bits(io.in, 6, 5)
    node _T_1083 = cat(_T_1081, UInt<3>(0))
    node _T_1084 = cat(_T_1079, _T_1080)
    node _T_1085 = cat(_T_1084, _T_1083)
    node _T_1088 = bits(io.in, 11, 7)
    node _T_1090 = cat(_T_1088, UInt<7>(7))
    node _T_1091 = cat(_T_1085, UInt<5>(2))
    node _T_1092 = cat(_T_1091, UInt<3>(3))
    node _T_1093 = cat(_T_1092, _T_1090)
    node _T_1094 = bits(io.in, 11, 7)
    node _T_1096 = bits(io.in, 6, 2)
    node _T_1097 = bits(io.in, 31, 27)
    wire _T_1104 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1104 is invalid
    _T_1104.bits_wky <= _T_1093
    _T_1104.rd <= _T_1094
    _T_1104.rs1 <= UInt<5>(2)
    _T_1104.rs2 <= _T_1096
    _T_1104.rs3 <= _T_1097
    node _T_1110 = bits(io.in, 3, 2)
    node _T_1111 = bits(io.in, 12, 12)
    node _T_1112 = bits(io.in, 6, 4)
    node _T_1114 = cat(_T_1112, UInt<2>(0))
    node _T_1115 = cat(_T_1110, _T_1111)
    node _T_1116 = cat(_T_1115, _T_1114)
    node _T_1119 = bits(io.in, 11, 7)
    node _T_1121 = cat(_T_1119, UInt<7>(3))
    node _T_1122 = cat(_T_1116, UInt<5>(2))
    node _T_1123 = cat(_T_1122, UInt<3>(2))
    node _T_1124 = cat(_T_1123, _T_1121)
    node _T_1125 = bits(io.in, 11, 7)
    node _T_1127 = bits(io.in, 6, 2)
    node _T_1128 = bits(io.in, 31, 27)
    wire _T_1135 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1135 is invalid
    _T_1135.bits_wky <= _T_1124
    _T_1135.rd <= _T_1125
    _T_1135.rs1 <= UInt<5>(2)
    _T_1135.rs2 <= _T_1127
    _T_1135.rs3 <= _T_1128
    node _T_1141 = bits(io.in, 4, 2)
    node _T_1142 = bits(io.in, 12, 12)
    node _T_1143 = bits(io.in, 6, 5)
    node _T_1145 = cat(_T_1143, UInt<3>(0))
    node _T_1146 = cat(_T_1141, _T_1142)
    node _T_1147 = cat(_T_1146, _T_1145)
    node _T_1150 = bits(io.in, 11, 7)
    node _T_1152 = cat(_T_1150, UInt<7>(3))
    node _T_1153 = cat(_T_1147, UInt<5>(2))
    node _T_1154 = cat(_T_1153, UInt<3>(3))
    node _T_1155 = cat(_T_1154, _T_1152)
    node _T_1156 = bits(io.in, 11, 7)
    node _T_1158 = bits(io.in, 6, 2)
    node _T_1159 = bits(io.in, 31, 27)
    wire _T_1166 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1166 is invalid
    _T_1166.bits_wky <= _T_1155
    _T_1166.rd <= _T_1156
    _T_1166.rs1 <= UInt<5>(2)
    _T_1166.rs2 <= _T_1158
    _T_1166.rs3 <= _T_1159
    node _T_1172 = bits(io.in, 6, 2)
    node _T_1175 = bits(io.in, 11, 7)
    node _T_1177 = cat(_T_1175, UInt<7>(51))
    node _T_1178 = cat(_T_1172, UInt<5>(0))
    node _T_1179 = cat(_T_1178, UInt<3>(0))
    node _T_1180 = cat(_T_1179, _T_1177)
    node _T_1181 = bits(io.in, 11, 7)
    node _T_1183 = bits(io.in, 6, 2)
    node _T_1184 = bits(io.in, 31, 27)
    wire _T_1191 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1191 is invalid
    _T_1191.bits_wky <= _T_1180
    _T_1191.rd <= _T_1181
    _T_1191.rs1 <= UInt<5>(0)
    _T_1191.rs2 <= _T_1183
    _T_1191.rs3 <= _T_1184
    node _T_1197 = bits(io.in, 6, 2)
    node _T_1198 = bits(io.in, 11, 7)
    node _T_1200 = bits(io.in, 11, 7)
    node _T_1202 = cat(_T_1200, UInt<7>(51))
    node _T_1203 = cat(_T_1197, _T_1198)
    node _T_1204 = cat(_T_1203, UInt<3>(0))
    node _T_1205 = cat(_T_1204, _T_1202)
    node _T_1206 = bits(io.in, 11, 7)
    node _T_1207 = bits(io.in, 11, 7)
    node _T_1208 = bits(io.in, 6, 2)
    node _T_1209 = bits(io.in, 31, 27)
    wire _T_1216 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1216 is invalid
    _T_1216.bits_wky <= _T_1205
    _T_1216.rd <= _T_1206
    _T_1216.rs1 <= _T_1207
    _T_1216.rs2 <= _T_1208
    _T_1216.rs3 <= _T_1209
    node _T_1222 = bits(io.in, 6, 2)
    node _T_1223 = bits(io.in, 11, 7)
    node _T_1227 = cat(UInt<5>(0), UInt<7>(103))
    node _T_1228 = cat(_T_1222, _T_1223)
    node _T_1229 = cat(_T_1228, UInt<3>(0))
    node _T_1230 = cat(_T_1229, _T_1227)
    node _T_1231 = shr(_T_1230, 7)
    node _T_1233 = cat(_T_1231, UInt<7>(31))
    node _T_1234 = bits(io.in, 11, 7)
    node _T_1236 = neq(_T_1234, UInt<1>(0))
    node _T_1237 = mux(_T_1236, _T_1230, _T_1233)
    node _T_1239 = bits(io.in, 11, 7)
    node _T_1240 = bits(io.in, 6, 2)
    node _T_1241 = bits(io.in, 31, 27)
    wire _T_1248 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1248 is invalid
    _T_1248.bits_wky <= _T_1237
    _T_1248.rd <= UInt<5>(0)
    _T_1248.rs1 <= _T_1239
    _T_1248.rs2 <= _T_1240
    _T_1248.rs3 <= _T_1241
    node _T_1254 = bits(io.in, 6, 2)
    node _T_1256 = neq(_T_1254, UInt<1>(0))
    node _T_1257 = mux(_T_1256, _T_1191, _T_1248)
    node _T_1263 = bits(io.in, 6, 2)
    node _T_1264 = bits(io.in, 11, 7)
    node _T_1268 = cat(UInt<5>(1), UInt<7>(103))
    node _T_1269 = cat(_T_1263, _T_1264)
    node _T_1270 = cat(_T_1269, UInt<3>(0))
    node _T_1271 = cat(_T_1270, _T_1268)
    node _T_1272 = shr(_T_1230, 7)
    node _T_1274 = cat(_T_1272, UInt<7>(115))
    node _T_1276 = or(_T_1274, UInt<21>(1048576))
    node _T_1277 = bits(io.in, 11, 7)
    node _T_1279 = neq(_T_1277, UInt<1>(0))
    node _T_1280 = mux(_T_1279, _T_1271, _T_1276)
    node _T_1282 = bits(io.in, 11, 7)
    node _T_1283 = bits(io.in, 6, 2)
    node _T_1284 = bits(io.in, 31, 27)
    wire _T_1291 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1291 is invalid
    _T_1291.bits_wky <= _T_1280
    _T_1291.rd <= UInt<5>(1)
    _T_1291.rs1 <= _T_1282
    _T_1291.rs2 <= _T_1283
    _T_1291.rs3 <= _T_1284
    node _T_1297 = bits(io.in, 6, 2)
    node _T_1299 = neq(_T_1297, UInt<1>(0))
    node _T_1300 = mux(_T_1299, _T_1216, _T_1291)
    node _T_1306 = bits(io.in, 12, 12)
    node _T_1307 = mux(_T_1306, _T_1300, _T_1257)
    node _T_1313 = bits(io.in, 9, 7)
    node _T_1314 = bits(io.in, 12, 10)
    node _T_1316 = cat(_T_1313, _T_1314)
    node _T_1317 = cat(_T_1316, UInt<3>(0))
    node _T_1318 = shr(_T_1317, 5)
    node _T_1319 = bits(io.in, 6, 2)
    node _T_1322 = bits(io.in, 9, 7)
    node _T_1323 = bits(io.in, 12, 10)
    node _T_1325 = cat(_T_1322, _T_1323)
    node _T_1326 = cat(_T_1325, UInt<3>(0))
    node _T_1327 = bits(_T_1326, 4, 0)
    node _T_1329 = cat(UInt<3>(3), _T_1327)
    node _T_1330 = cat(_T_1329, UInt<7>(39))
    node _T_1331 = cat(_T_1318, _T_1319)
    node _T_1332 = cat(_T_1331, UInt<5>(2))
    node _T_1333 = cat(_T_1332, _T_1330)
    node _T_1334 = bits(io.in, 11, 7)
    node _T_1336 = bits(io.in, 6, 2)
    node _T_1337 = bits(io.in, 31, 27)
    wire _T_1344 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1344 is invalid
    _T_1344.bits_wky <= _T_1333
    _T_1344.rd <= _T_1334
    _T_1344.rs1 <= UInt<5>(2)
    _T_1344.rs2 <= _T_1336
    _T_1344.rs3 <= _T_1337
    node _T_1350 = bits(io.in, 8, 7)
    node _T_1351 = bits(io.in, 12, 9)
    node _T_1353 = cat(_T_1350, _T_1351)
    node _T_1354 = cat(_T_1353, UInt<2>(0))
    node _T_1355 = shr(_T_1354, 5)
    node _T_1356 = bits(io.in, 6, 2)
    node _T_1359 = bits(io.in, 8, 7)
    node _T_1360 = bits(io.in, 12, 9)
    node _T_1362 = cat(_T_1359, _T_1360)
    node _T_1363 = cat(_T_1362, UInt<2>(0))
    node _T_1364 = bits(_T_1363, 4, 0)
    node _T_1366 = cat(UInt<3>(2), _T_1364)
    node _T_1367 = cat(_T_1366, UInt<7>(35))
    node _T_1368 = cat(_T_1355, _T_1356)
    node _T_1369 = cat(_T_1368, UInt<5>(2))
    node _T_1370 = cat(_T_1369, _T_1367)
    node _T_1371 = bits(io.in, 11, 7)
    node _T_1373 = bits(io.in, 6, 2)
    node _T_1374 = bits(io.in, 31, 27)
    wire _T_1381 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1381 is invalid
    _T_1381.bits_wky <= _T_1370
    _T_1381.rd <= _T_1371
    _T_1381.rs1 <= UInt<5>(2)
    _T_1381.rs2 <= _T_1373
    _T_1381.rs3 <= _T_1374
    node _T_1387 = bits(io.in, 9, 7)
    node _T_1388 = bits(io.in, 12, 10)
    node _T_1390 = cat(_T_1387, _T_1388)
    node _T_1391 = cat(_T_1390, UInt<3>(0))
    node _T_1392 = shr(_T_1391, 5)
    node _T_1393 = bits(io.in, 6, 2)
    node _T_1396 = bits(io.in, 9, 7)
    node _T_1397 = bits(io.in, 12, 10)
    node _T_1399 = cat(_T_1396, _T_1397)
    node _T_1400 = cat(_T_1399, UInt<3>(0))
    node _T_1401 = bits(_T_1400, 4, 0)
    node _T_1403 = cat(UInt<3>(3), _T_1401)
    node _T_1404 = cat(_T_1403, UInt<7>(35))
    node _T_1405 = cat(_T_1392, _T_1393)
    node _T_1406 = cat(_T_1405, UInt<5>(2))
    node _T_1407 = cat(_T_1406, _T_1404)
    node _T_1408 = bits(io.in, 11, 7)
    node _T_1410 = bits(io.in, 6, 2)
    node _T_1411 = bits(io.in, 31, 27)
    wire _T_1418 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1418 is invalid
    _T_1418.bits_wky <= _T_1407
    _T_1418.rd <= _T_1408
    _T_1418.rs1 <= UInt<5>(2)
    _T_1418.rs2 <= _T_1410
    _T_1418.rs3 <= _T_1411
    node _T_1424 = bits(io.in, 11, 7)
    node _T_1425 = bits(io.in, 19, 15)
    node _T_1426 = bits(io.in, 24, 20)
    node _T_1427 = bits(io.in, 31, 27)
    wire _T_1434 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1434 is invalid
    _T_1434.bits_wky <= io.in
    _T_1434.rd <= _T_1424
    _T_1434.rs1 <= _T_1425
    _T_1434.rs2 <= _T_1426
    _T_1434.rs3 <= _T_1427
    node _T_1440 = bits(io.in, 11, 7)
    node _T_1441 = bits(io.in, 19, 15)
    node _T_1442 = bits(io.in, 24, 20)
    node _T_1443 = bits(io.in, 31, 27)
    wire _T_1450 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1450 is invalid
    _T_1450.bits_wky <= io.in
    _T_1450.rd <= _T_1440
    _T_1450.rs1 <= _T_1441
    _T_1450.rs2 <= _T_1442
    _T_1450.rs3 <= _T_1443
    node _T_1456 = bits(io.in, 11, 7)
    node _T_1457 = bits(io.in, 19, 15)
    node _T_1458 = bits(io.in, 24, 20)
    node _T_1459 = bits(io.in, 31, 27)
    wire _T_1466 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1466 is invalid
    _T_1466.bits_wky <= io.in
    _T_1466.rd <= _T_1456
    _T_1466.rs1 <= _T_1457
    _T_1466.rs2 <= _T_1458
    _T_1466.rs3 <= _T_1459
    node _T_1472 = bits(io.in, 11, 7)
    node _T_1473 = bits(io.in, 19, 15)
    node _T_1474 = bits(io.in, 24, 20)
    node _T_1475 = bits(io.in, 31, 27)
    wire _T_1482 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1482 is invalid
    _T_1482.bits_wky <= io.in
    _T_1482.rd <= _T_1472
    _T_1482.rs1 <= _T_1473
    _T_1482.rs2 <= _T_1474
    _T_1482.rs3 <= _T_1475
    node _T_1488 = bits(io.in, 11, 7)
    node _T_1489 = bits(io.in, 19, 15)
    node _T_1490 = bits(io.in, 24, 20)
    node _T_1491 = bits(io.in, 31, 27)
    wire _T_1498 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1498 is invalid
    _T_1498.bits_wky <= io.in
    _T_1498.rd <= _T_1488
    _T_1498.rs1 <= _T_1489
    _T_1498.rs2 <= _T_1490
    _T_1498.rs3 <= _T_1491
    node _T_1504 = bits(io.in, 11, 7)
    node _T_1505 = bits(io.in, 19, 15)
    node _T_1506 = bits(io.in, 24, 20)
    node _T_1507 = bits(io.in, 31, 27)
    wire _T_1514 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1514 is invalid
    _T_1514.bits_wky <= io.in
    _T_1514.rd <= _T_1504
    _T_1514.rs1 <= _T_1505
    _T_1514.rs2 <= _T_1506
    _T_1514.rs3 <= _T_1507
    node _T_1520 = bits(io.in, 11, 7)
    node _T_1521 = bits(io.in, 19, 15)
    node _T_1522 = bits(io.in, 24, 20)
    node _T_1523 = bits(io.in, 31, 27)
    wire _T_1530 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1530 is invalid
    _T_1530.bits_wky <= io.in
    _T_1530.rd <= _T_1520
    _T_1530.rs1 <= _T_1521
    _T_1530.rs2 <= _T_1522
    _T_1530.rs3 <= _T_1523
    node _T_1536 = bits(io.in, 11, 7)
    node _T_1537 = bits(io.in, 19, 15)
    node _T_1538 = bits(io.in, 24, 20)
    node _T_1539 = bits(io.in, 31, 27)
    wire _T_1546 : {bits_wky : UInt<32>, rd : UInt<5>, rs1 : UInt<5>, rs2 : UInt<5>, rs3 : UInt<5>}
    _T_1546 is invalid
    _T_1546.bits_wky <= io.in
    _T_1546.rd <= _T_1536
    _T_1546.rs1 <= _T_1537
    _T_1546.rs2 <= _T_1538
    _T_1546.rs3 <= _T_1539
    node _T_1552 = bits(io.in, 1, 0)
    node _T_1553 = bits(io.in, 15, 13)
    node _T_1554 = cat(_T_1552, _T_1553)
    node _T_1556 = and(_T_1554, UInt<4>(15))
    node _T_1558 = geq(_T_1554, UInt<5>(16))
    node _T_1560 = and(_T_1556, UInt<3>(7))
    node _T_1562 = geq(_T_1556, UInt<4>(8))
    node _T_1564 = and(_T_1560, UInt<2>(3))
    node _T_1566 = geq(_T_1560, UInt<3>(4))
    node _T_1568 = and(_T_1564, UInt<1>(1))
    node _T_1570 = geq(_T_1564, UInt<2>(2))
    node _T_1572 = and(_T_1568, UInt<1>(0))
    node _T_1574 = geq(_T_1568, UInt<1>(1))
    node _T_1575 = mux(_T_1574, _T_1546, _T_1530)
    node _T_1582 = and(_T_1568, UInt<1>(0))
    node _T_1584 = geq(_T_1568, UInt<1>(1))
    node _T_1585 = mux(_T_1584, _T_1514, _T_1498)
    node _T_1591 = mux(_T_1570, _T_1575, _T_1585)
    node _T_1598 = and(_T_1564, UInt<1>(1))
    node _T_1600 = geq(_T_1564, UInt<2>(2))
    node _T_1602 = and(_T_1598, UInt<1>(0))
    node _T_1604 = geq(_T_1598, UInt<1>(1))
    node _T_1605 = mux(_T_1604, _T_1482, _T_1466)
    node _T_1612 = and(_T_1598, UInt<1>(0))
    node _T_1614 = geq(_T_1598, UInt<1>(1))
    node _T_1615 = mux(_T_1614, _T_1450, _T_1434)
    node _T_1621 = mux(_T_1600, _T_1605, _T_1615)
    node _T_1627 = mux(_T_1566, _T_1591, _T_1621)
    node _T_1634 = and(_T_1560, UInt<2>(3))
    node _T_1636 = geq(_T_1560, UInt<3>(4))
    node _T_1638 = and(_T_1634, UInt<1>(1))
    node _T_1640 = geq(_T_1634, UInt<2>(2))
    node _T_1642 = and(_T_1638, UInt<1>(0))
    node _T_1644 = geq(_T_1638, UInt<1>(1))
    node _T_1645 = mux(_T_1644, _T_1418, _T_1381)
    node _T_1652 = and(_T_1638, UInt<1>(0))
    node _T_1654 = geq(_T_1638, UInt<1>(1))
    node _T_1655 = mux(_T_1654, _T_1344, _T_1307)
    node _T_1661 = mux(_T_1640, _T_1645, _T_1655)
    node _T_1668 = and(_T_1634, UInt<1>(1))
    node _T_1670 = geq(_T_1634, UInt<2>(2))
    node _T_1672 = and(_T_1668, UInt<1>(0))
    node _T_1674 = geq(_T_1668, UInt<1>(1))
    node _T_1675 = mux(_T_1674, _T_1166, _T_1135)
    node _T_1682 = and(_T_1668, UInt<1>(0))
    node _T_1684 = geq(_T_1668, UInt<1>(1))
    node _T_1685 = mux(_T_1684, _T_1104, _T_1073)
    node _T_1691 = mux(_T_1670, _T_1675, _T_1685)
    node _T_1697 = mux(_T_1636, _T_1661, _T_1691)
    node _T_1703 = mux(_T_1562, _T_1627, _T_1697)
    node _T_1710 = and(_T_1556, UInt<3>(7))
    node _T_1712 = geq(_T_1556, UInt<4>(8))
    node _T_1714 = and(_T_1710, UInt<2>(3))
    node _T_1716 = geq(_T_1710, UInt<3>(4))
    node _T_1718 = and(_T_1714, UInt<1>(1))
    node _T_1720 = geq(_T_1714, UInt<2>(2))
    node _T_1722 = and(_T_1718, UInt<1>(0))
    node _T_1724 = geq(_T_1718, UInt<1>(1))
    node _T_1725 = mux(_T_1724, _T_1046, _T_951)
    node _T_1732 = and(_T_1718, UInt<1>(0))
    node _T_1734 = geq(_T_1718, UInt<1>(1))
    node _T_1735 = mux(_T_1734, _T_854, _T_739)
    node _T_1741 = mux(_T_1720, _T_1725, _T_1735)
    node _T_1748 = and(_T_1714, UInt<1>(1))
    node _T_1750 = geq(_T_1714, UInt<2>(2))
    node _T_1752 = and(_T_1748, UInt<1>(0))
    node _T_1754 = geq(_T_1748, UInt<1>(1))
    node _T_1755 = mux(_T_1754, _T_580, _T_472)
    node _T_1762 = and(_T_1748, UInt<1>(0))
    node _T_1764 = geq(_T_1748, UInt<1>(1))
    node _T_1765 = mux(_T_1764, _T_439, _T_401)
    node _T_1771 = mux(_T_1750, _T_1755, _T_1765)
    node _T_1777 = mux(_T_1716, _T_1741, _T_1771)
    node _T_1784 = and(_T_1710, UInt<2>(3))
    node _T_1786 = geq(_T_1710, UInt<3>(4))
    node _T_1788 = and(_T_1784, UInt<1>(1))
    node _T_1790 = geq(_T_1784, UInt<2>(2))
    node _T_1792 = and(_T_1788, UInt<1>(0))
    node _T_1794 = geq(_T_1788, UInt<1>(1))
    node _T_1795 = mux(_T_1794, _T_368, _T_321)
    node _T_1802 = and(_T_1788, UInt<1>(0))
    node _T_1804 = geq(_T_1788, UInt<1>(1))
    node _T_1805 = mux(_T_1804, _T_270, _T_223)
    node _T_1811 = mux(_T_1790, _T_1795, _T_1805)
    node _T_1818 = and(_T_1784, UInt<1>(1))
    node _T_1820 = geq(_T_1784, UInt<2>(2))
    node _T_1822 = and(_T_1818, UInt<1>(0))
    node _T_1824 = geq(_T_1818, UInt<1>(1))
    node _T_1825 = mux(_T_1824, _T_172, _T_133)
    node _T_1832 = and(_T_1818, UInt<1>(0))
    node _T_1834 = geq(_T_1818, UInt<1>(1))
    node _T_1835 = mux(_T_1834, _T_92, _T_53)
    node _T_1841 = mux(_T_1820, _T_1825, _T_1835)
    node _T_1847 = mux(_T_1786, _T_1811, _T_1841)
    node _T_1853 = mux(_T_1712, _T_1777, _T_1847)
    node _T_1859 = mux(_T_1558, _T_1703, _T_1853)
    io.out <= _T_1859
