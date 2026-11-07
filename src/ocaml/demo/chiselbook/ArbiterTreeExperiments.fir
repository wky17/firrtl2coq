circuit ArbiterTreeExperiments :
  module ArbiterTreeExperiments :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip in : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>}[7], out : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>}}

    reg io_out_regData : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_io_in_1_ready_T = eq(io_out_regState, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io.in[1].ready <= _io_out_io_in_1_ready_T @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_io_in_2_ready_T = eq(io_out_regState, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io.in[2].ready <= _io_out_io_in_2_ready_T @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T = eq(io_out_regState, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_1 = eq(io_out_regState, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_2 = or(_io_out_out_valid_T, _io_out_out_valid_T_1) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out.valid <= _io_out_out_valid_T_2 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_1 = asUInt(io_out_regState) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_2 = eq(_io_out_T, _io_out_T_1) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_2 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io.in[1].valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData <= io.in[1].bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_3 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_4 = asUInt(io_out_regState) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_5 = eq(_io_out_T_3, _io_out_T_4) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_5 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io.in[2].valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData <= io.in[2].bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_6 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_7 = asUInt(io_out_regState) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_8 = eq(_io_out_T_6, _io_out_T_7) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_8 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_9 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_10 = asUInt(io_out_regState) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_11 = eq(_io_out_T_9, _io_out_T_10) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_11 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out.bits_wky <= io_out_regData @[ArbiterTreeExperiements.scala 144:14]
    reg io_out_regData_1 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_1) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState_1 : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out_1 : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_io_in_3_ready_T = eq(io_out_regState_1, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io.in[3].ready <= _io_out_io_in_3_ready_T @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_io_in_4_ready_T = eq(io_out_regState_1, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io.in[4].ready <= _io_out_io_in_4_ready_T @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T_3 = eq(io_out_regState_1, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_4 = eq(io_out_regState_1, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_5 = or(_io_out_out_valid_T_3, _io_out_out_valid_T_4) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out_1.valid <= _io_out_out_valid_T_5 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T_12 = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_13 = asUInt(io_out_regState_1) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_14 = eq(_io_out_T_12, _io_out_T_13) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_14 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io.in[3].valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData_1 <= io.in[3].bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState_1 <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState_1 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_15 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_16 = asUInt(io_out_regState_1) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_17 = eq(_io_out_T_15, _io_out_T_16) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_17 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io.in[4].valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData_1 <= io.in[4].bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState_1 <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState_1 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_18 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_19 = asUInt(io_out_regState_1) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_20 = eq(_io_out_T_18, _io_out_T_19) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_20 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out_1.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState_1 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_21 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_22 = asUInt(io_out_regState_1) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_23 = eq(_io_out_T_21, _io_out_T_22) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_23 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out_1.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState_1 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out_1.bits_wky <= io_out_regData_1 @[ArbiterTreeExperiements.scala 144:14]
    reg io_out_regData_2 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_2) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState_2 : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out_2 : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_io_in_5_ready_T = eq(io_out_regState_2, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io.in[5].ready <= _io_out_io_in_5_ready_T @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_io_in_6_ready_T = eq(io_out_regState_2, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io.in[6].ready <= _io_out_io_in_6_ready_T @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T_6 = eq(io_out_regState_2, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_7 = eq(io_out_regState_2, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_8 = or(_io_out_out_valid_T_6, _io_out_out_valid_T_7) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out_2.valid <= _io_out_out_valid_T_8 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T_24 = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_25 = asUInt(io_out_regState_2) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_26 = eq(_io_out_T_24, _io_out_T_25) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_26 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io.in[5].valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData_2 <= io.in[5].bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState_2 <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState_2 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_27 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_28 = asUInt(io_out_regState_2) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_29 = eq(_io_out_T_27, _io_out_T_28) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_29 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io.in[6].valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData_2 <= io.in[6].bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState_2 <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState_2 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_30 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_31 = asUInt(io_out_regState_2) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_32 = eq(_io_out_T_30, _io_out_T_31) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_32 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out_2.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState_2 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_33 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_34 = asUInt(io_out_regState_2) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_35 = eq(_io_out_T_33, _io_out_T_34) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_35 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out_2.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState_2 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out_2.bits_wky <= io_out_regData_2 @[ArbiterTreeExperiements.scala 144:14]
    reg io_out_regData_3 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_3) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState_3 : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out_3 : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_io_in_0_ready_T = eq(io_out_regState_3, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io.in[0].ready <= _io_out_io_in_0_ready_T @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_out_ready_T = eq(io_out_regState_3, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io_out_out.ready <= _io_out_out_ready_T @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T_9 = eq(io_out_regState_3, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_10 = eq(io_out_regState_3, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_11 = or(_io_out_out_valid_T_9, _io_out_out_valid_T_10) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out_3.valid <= _io_out_out_valid_T_11 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T_36 = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_37 = asUInt(io_out_regState_3) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_38 = eq(_io_out_T_36, _io_out_T_37) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_38 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io.in[0].valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData_3 <= io.in[0].bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState_3 <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState_3 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_39 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_40 = asUInt(io_out_regState_3) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_41 = eq(_io_out_T_39, _io_out_T_40) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_41 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io_out_out.valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData_3 <= io_out_out.bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState_3 <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState_3 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_42 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_43 = asUInt(io_out_regState_3) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_44 = eq(_io_out_T_42, _io_out_T_43) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_44 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out_3.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState_3 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_45 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_46 = asUInt(io_out_regState_3) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_47 = eq(_io_out_T_45, _io_out_T_46) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_47 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out_3.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState_3 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out_3.bits_wky <= io_out_regData_3 @[ArbiterTreeExperiements.scala 144:14]
    reg io_out_regData_4 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_4) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState_4 : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out_4 : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_out_ready_T_1 = eq(io_out_regState_4, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io_out_out_1.ready <= _io_out_out_ready_T_1 @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_out_ready_T_2 = eq(io_out_regState_4, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io_out_out_2.ready <= _io_out_out_ready_T_2 @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T_12 = eq(io_out_regState_4, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_13 = eq(io_out_regState_4, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_14 = or(_io_out_out_valid_T_12, _io_out_out_valid_T_13) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out_4.valid <= _io_out_out_valid_T_14 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T_48 = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_49 = asUInt(io_out_regState_4) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_50 = eq(_io_out_T_48, _io_out_T_49) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_50 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io_out_out_1.valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData_4 <= io_out_out_1.bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState_4 <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState_4 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_51 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_52 = asUInt(io_out_regState_4) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_53 = eq(_io_out_T_51, _io_out_T_52) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_53 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io_out_out_2.valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData_4 <= io_out_out_2.bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState_4 <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState_4 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_54 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_55 = asUInt(io_out_regState_4) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_56 = eq(_io_out_T_54, _io_out_T_55) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_56 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out_4.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState_4 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_57 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_58 = asUInt(io_out_regState_4) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_59 = eq(_io_out_T_57, _io_out_T_58) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_59 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out_4.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState_4 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out_4.bits_wky <= io_out_regData_4 @[ArbiterTreeExperiements.scala 144:14]
    reg io_out_regData_5 : UInt<8>, clock with :
      reset => (UInt<1>("h0"), io_out_regData_5) @[ArbiterTreeExperiements.scala 107:22]
    reg io_out_regState_5 : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 108:27]
    wire io_out_out_5 : { flip ready : UInt<1>, valid : UInt<1>, bits_wky : UInt<8>} @[ArbiterTreeExperiements.scala 109:19]
    node _io_out_out_ready_T_3 = eq(io_out_regState_5, UInt<1>("h0")) @[ArbiterTreeExperiements.scala 111:25]
    io_out_out_3.ready <= _io_out_out_ready_T_3 @[ArbiterTreeExperiements.scala 111:13]
    node _io_out_out_ready_T_4 = eq(io_out_regState_5, UInt<1>("h1")) @[ArbiterTreeExperiements.scala 112:25]
    io_out_out_4.ready <= _io_out_out_ready_T_4 @[ArbiterTreeExperiements.scala 112:13]
    node _io_out_out_valid_T_15 = eq(io_out_regState_5, UInt<2>("h2")) @[ArbiterTreeExperiements.scala 113:28]
    node _io_out_out_valid_T_16 = eq(io_out_regState_5, UInt<2>("h3")) @[ArbiterTreeExperiements.scala 113:49]
    node _io_out_out_valid_T_17 = or(_io_out_out_valid_T_15, _io_out_out_valid_T_16) @[ArbiterTreeExperiements.scala 113:37]
    io_out_out_5.valid <= _io_out_out_valid_T_17 @[ArbiterTreeExperiements.scala 113:15]
    node _io_out_T_60 = asUInt(UInt<1>("h0")) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_61 = asUInt(io_out_regState_5) @[ArbiterTreeExperiements.scala 115:22]
    node _io_out_T_62 = eq(_io_out_T_60, _io_out_T_61) @[ArbiterTreeExperiements.scala 115:22]
    when _io_out_T_62 : @[ArbiterTreeExperiements.scala 115:22]
    {
      when io_out_out_3.valid : @[ArbiterTreeExperiements.scala 117:24]
      {
        io_out_regData_5 <= io_out_out_3.bits_wky @[ArbiterTreeExperiements.scala 118:19]
        io_out_regState_5 <= UInt<2>("h2") @[ArbiterTreeExperiements.scala 119:20]
      }
      else :
      {
        io_out_regState_5 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 121:20]
    }
    }
    else :
    {
      node _io_out_T_63 = asUInt(UInt<1>("h1")) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_64 = asUInt(io_out_regState_5) @[ArbiterTreeExperiements.scala 115:22]
      node _io_out_T_65 = eq(_io_out_T_63, _io_out_T_64) @[ArbiterTreeExperiements.scala 115:22]
      when _io_out_T_65 : @[ArbiterTreeExperiements.scala 115:22]
      {
        when io_out_out_4.valid : @[ArbiterTreeExperiements.scala 125:24]
        {
          io_out_regData_5 <= io_out_out_4.bits_wky @[ArbiterTreeExperiements.scala 126:19]
          io_out_regState_5 <= UInt<2>("h3") @[ArbiterTreeExperiements.scala 127:20]
        }
        else :
        {
          io_out_regState_5 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 129:20]
      }
      }
      else :
      {
        node _io_out_T_66 = asUInt(UInt<2>("h2")) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_67 = asUInt(io_out_regState_5) @[ArbiterTreeExperiements.scala 115:22]
        node _io_out_T_68 = eq(_io_out_T_66, _io_out_T_67) @[ArbiterTreeExperiements.scala 115:22]
        when _io_out_T_68 : @[ArbiterTreeExperiements.scala 115:22]
        {
          when io_out_out_5.ready : @[ArbiterTreeExperiements.scala 133:26]
          {
            io_out_regState_5 <= UInt<1>("h1") @[ArbiterTreeExperiements.scala 134:20]
        }
        }
        else :
        {
          node _io_out_T_69 = asUInt(UInt<2>("h3")) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_70 = asUInt(io_out_regState_5) @[ArbiterTreeExperiements.scala 115:22]
          node _io_out_T_71 = eq(_io_out_T_69, _io_out_T_70) @[ArbiterTreeExperiements.scala 115:22]
          when _io_out_T_71 : @[ArbiterTreeExperiements.scala 115:22]
          {
            when io_out_out_5.ready : @[ArbiterTreeExperiements.scala 138:26]
            {
              io_out_regState_5 <= UInt<1>("h0") @[ArbiterTreeExperiements.scala 139:20]
    }
    }
    }
    }
    }
    io_out_out_5.bits_wky <= io_out_regData_5 @[ArbiterTreeExperiements.scala 144:14]
    io.out <= io_out_out_5 @[ArbiterTreeExperiements.scala 159:10]

