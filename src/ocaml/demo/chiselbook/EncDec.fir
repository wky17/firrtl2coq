circuit EncDec :
  module EncDec :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip decin : UInt<2>, decout : UInt<4>, flip encin : UInt<4>, encout : UInt<2>, flip largeEncIn : UInt<16>, largeEncOut : UInt<4>}

    wire result : UInt<4> @[EncDec.scala 19:20]
    result <= UInt<1>("h0") @[EncDec.scala 22:10]
    node _T = eq(UInt<1>("h0"), io.decin) @[EncDec.scala 24:15]
    when _T : @[EncDec.scala 24:15]
    {
      result <= UInt<1>("h1") @[EncDec.scala 25:23]
    }
    else :
    {
      node _T_1 = eq(UInt<1>("h1"), io.decin) @[EncDec.scala 24:15]
      when _T_1 : @[EncDec.scala 24:15]
      {
        result <= UInt<2>("h2") @[EncDec.scala 26:23]
      }
      else :
      {
        node _T_2 = eq(UInt<2>("h2"), io.decin) @[EncDec.scala 24:15]
        when _T_2 : @[EncDec.scala 24:15]
        {
          result <= UInt<3>("h4") @[EncDec.scala 27:23]
        }
        else :
        {
          node _T_3 = eq(UInt<2>("h3"), io.decin) @[EncDec.scala 24:15]
          when _T_3 : @[EncDec.scala 24:15]
          {
            result <= UInt<4>("h8") @[EncDec.scala 28:23]
    }
    }
    }
    }
    node _T_4 = eq(UInt<1>("h0"), io.decin) @[EncDec.scala 33:16]
    when _T_4 : @[EncDec.scala 33:16]
    {
      result <= UInt<1>("h1") @[EncDec.scala 34:27]
    }
    else :
    {
      node _T_5 = eq(UInt<1>("h1"), io.decin) @[EncDec.scala 33:16]
      when _T_5 : @[EncDec.scala 33:16]
      {
        result <= UInt<2>("h2") @[EncDec.scala 35:27]
      }
      else :
      {
        node _T_6 = eq(UInt<2>("h2"), io.decin) @[EncDec.scala 33:16]
        when _T_6 : @[EncDec.scala 33:16]
        {
          result <= UInt<3>("h4") @[EncDec.scala 36:27]
        }
        else :
        {
          node _T_7 = eq(UInt<2>("h3"), io.decin) @[EncDec.scala 33:16]
          when _T_7 : @[EncDec.scala 33:16]
          {
            result <= UInt<4>("h8") @[EncDec.scala 37:27]
    }
    }
    }
    }
    node _result_T = dshl(UInt<1>("h1"), io.decin) @[EncDec.scala 42:17]
    result <= _result_T @[EncDec.scala 42:10]
    io.decout <= result @[EncDec.scala 45:13]
    wire b : UInt<2> @[EncDec.scala 48:15]
    b <= UInt<1>("h0") @[EncDec.scala 50:5]
    node _T_8 = eq(UInt<1>("h1"), io.encin) @[EncDec.scala 51:14]
    when _T_8 : @[EncDec.scala 51:14]
    {
      b <= UInt<1>("h0") @[EncDec.scala 52:24]
    }
    else :
    {
      node _T_9 = eq(UInt<2>("h2"), io.encin) @[EncDec.scala 51:14]
      when _T_9 : @[EncDec.scala 51:14]
      {
        b <= UInt<1>("h1") @[EncDec.scala 53:24]
      }
      else :
      {
        node _T_10 = eq(UInt<3>("h4"), io.encin) @[EncDec.scala 51:14]
        when _T_10 : @[EncDec.scala 51:14]
        {
          b <= UInt<2>("h2") @[EncDec.scala 54:24]
        }
        else :
        {
          node _T_11 = eq(UInt<4>("h8"), io.encin) @[EncDec.scala 51:14]
          when _T_11 : @[EncDec.scala 51:14]
          {
            b <= UInt<2>("h3") @[EncDec.scala 55:24]
    }
    }
    }
    }
    io.encout <= b @[EncDec.scala 59:13]
    wire v : UInt<4>[16] @[EncDec.scala 64:15]
    v[0] <= UInt<1>("h0") @[EncDec.scala 65:8]
    node _v_1_T = bits(io.largeEncIn, 1, 1) @[EncDec.scala 67:22]
    node _v_1_T_1 = mux(_v_1_T, UInt<1>("h1"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_1_T_2 = or(_v_1_T_1, v[0]) @[EncDec.scala 67:37]
    v[1] <= _v_1_T_2 @[EncDec.scala 67:10]
    node _v_2_T = bits(io.largeEncIn, 2, 2) @[EncDec.scala 67:22]
    node _v_2_T_1 = mux(_v_2_T, UInt<2>("h2"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_2_T_2 = or(_v_2_T_1, v[1]) @[EncDec.scala 67:37]
    v[2] <= _v_2_T_2 @[EncDec.scala 67:10]
    node _v_3_T = bits(io.largeEncIn, 3, 3) @[EncDec.scala 67:22]
    node _v_3_T_1 = mux(_v_3_T, UInt<2>("h3"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_3_T_2 = or(_v_3_T_1, v[2]) @[EncDec.scala 67:37]
    v[3] <= _v_3_T_2 @[EncDec.scala 67:10]
    node _v_4_T = bits(io.largeEncIn, 4, 4) @[EncDec.scala 67:22]
    node _v_4_T_1 = mux(_v_4_T, UInt<3>("h4"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_4_T_2 = or(_v_4_T_1, v[3]) @[EncDec.scala 67:37]
    v[4] <= _v_4_T_2 @[EncDec.scala 67:10]
    node _v_5_T = bits(io.largeEncIn, 5, 5) @[EncDec.scala 67:22]
    node _v_5_T_1 = mux(_v_5_T, UInt<3>("h5"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_5_T_2 = or(_v_5_T_1, v[4]) @[EncDec.scala 67:37]
    v[5] <= _v_5_T_2 @[EncDec.scala 67:10]
    node _v_6_T = bits(io.largeEncIn, 6, 6) @[EncDec.scala 67:22]
    node _v_6_T_1 = mux(_v_6_T, UInt<3>("h6"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_6_T_2 = or(_v_6_T_1, v[5]) @[EncDec.scala 67:37]
    v[6] <= _v_6_T_2 @[EncDec.scala 67:10]
    node _v_7_T = bits(io.largeEncIn, 7, 7) @[EncDec.scala 67:22]
    node _v_7_T_1 = mux(_v_7_T, UInt<3>("h7"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_7_T_2 = or(_v_7_T_1, v[6]) @[EncDec.scala 67:37]
    v[7] <= _v_7_T_2 @[EncDec.scala 67:10]
    node _v_8_T = bits(io.largeEncIn, 8, 8) @[EncDec.scala 67:22]
    node _v_8_T_1 = mux(_v_8_T, UInt<4>("h8"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_8_T_2 = or(_v_8_T_1, v[7]) @[EncDec.scala 67:37]
    v[8] <= _v_8_T_2 @[EncDec.scala 67:10]
    node _v_9_T = bits(io.largeEncIn, 9, 9) @[EncDec.scala 67:22]
    node _v_9_T_1 = mux(_v_9_T, UInt<4>("h9"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_9_T_2 = or(_v_9_T_1, v[8]) @[EncDec.scala 67:37]
    v[9] <= _v_9_T_2 @[EncDec.scala 67:10]
    node _v_10_T = bits(io.largeEncIn, 10, 10) @[EncDec.scala 67:22]
    node _v_10_T_1 = mux(_v_10_T, UInt<4>("ha"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_10_T_2 = or(_v_10_T_1, v[9]) @[EncDec.scala 67:37]
    v[10] <= _v_10_T_2 @[EncDec.scala 67:10]
    node _v_11_T = bits(io.largeEncIn, 11, 11) @[EncDec.scala 67:22]
    node _v_11_T_1 = mux(_v_11_T, UInt<4>("hb"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_11_T_2 = or(_v_11_T_1, v[10]) @[EncDec.scala 67:37]
    v[11] <= _v_11_T_2 @[EncDec.scala 67:10]
    node _v_12_T = bits(io.largeEncIn, 12, 12) @[EncDec.scala 67:22]
    node _v_12_T_1 = mux(_v_12_T, UInt<4>("hc"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_12_T_2 = or(_v_12_T_1, v[11]) @[EncDec.scala 67:37]
    v[12] <= _v_12_T_2 @[EncDec.scala 67:10]
    node _v_13_T = bits(io.largeEncIn, 13, 13) @[EncDec.scala 67:22]
    node _v_13_T_1 = mux(_v_13_T, UInt<4>("hd"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_13_T_2 = or(_v_13_T_1, v[12]) @[EncDec.scala 67:37]
    v[13] <= _v_13_T_2 @[EncDec.scala 67:10]
    node _v_14_T = bits(io.largeEncIn, 14, 14) @[EncDec.scala 67:22]
    node _v_14_T_1 = mux(_v_14_T, UInt<4>("he"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_14_T_2 = or(_v_14_T_1, v[13]) @[EncDec.scala 67:37]
    v[14] <= _v_14_T_2 @[EncDec.scala 67:10]
    node _v_15_T = bits(io.largeEncIn, 15, 15) @[EncDec.scala 67:22]
    node _v_15_T_1 = mux(_v_15_T, UInt<4>("hf"), UInt<1>("h0")) @[EncDec.scala 67:16]
    node _v_15_T_2 = or(_v_15_T_1, v[14]) @[EncDec.scala 67:37]
    v[15] <= _v_15_T_2 @[EncDec.scala 67:10]
    io.largeEncOut <= v[15] @[EncDec.scala 71:18]

