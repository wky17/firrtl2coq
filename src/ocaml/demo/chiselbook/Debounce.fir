circuit Debounce :
  module Debounce :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip btnU : UInt<1>, led : UInt<8>}

    reg btnSync_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnSync_REG) @[Debounce.scala 13:32]
    btnSync_REG <= io.btnU @[Debounce.scala 13:32]
    reg btnSync : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnSync) @[Debounce.scala 13:24]
    btnSync <= btnSync_REG @[Debounce.scala 13:24]
    reg btnDebReg : UInt<1>, clock with :
      reset => (UInt<1>("h0"), btnDebReg) @[Debounce.scala 24:22]
    reg cntReg : UInt<32>, clock with :
      reset => (reset_wky, UInt<32>("h0")) @[Debounce.scala 26:23]
    node tick = eq(cntReg, UInt<20>("hf423f")) @[Debounce.scala 27:21]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Debounce.scala 29:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Debounce.scala 29:20]
    cntReg <= _cntReg_T_1 @[Debounce.scala 29:10]
    when tick : @[Debounce.scala 30:15]
    {
      cntReg <= UInt<1>("h0") @[Debounce.scala 31:12]
      btnDebReg <= btnSync @[Debounce.scala 32:15]
    }
    reg shiftReg : UInt<3>, clock with :
      reset => (reset_wky, UInt<3>("h0")) @[Debounce.scala 37:25]
    when tick : @[Debounce.scala 38:15]
    {
      node _shiftReg_T = bits(shiftReg, 1, 0) @[Debounce.scala 40:25]
      node _shiftReg_T_1 = cat(_shiftReg_T, btnDebReg) @[Debounce.scala 40:32]
      shiftReg <= _shiftReg_T_1 @[Debounce.scala 40:14]
    }
    node _btnClean_T = bits(shiftReg, 2, 2) @[Debounce.scala 43:27]
    node _btnClean_T_1 = bits(shiftReg, 1, 1) @[Debounce.scala 43:41]
    node _btnClean_T_2 = and(_btnClean_T, _btnClean_T_1) @[Debounce.scala 43:31]
    node _btnClean_T_3 = bits(shiftReg, 2, 2) @[Debounce.scala 43:57]
    node _btnClean_T_4 = bits(shiftReg, 0, 0) @[Debounce.scala 43:71]
    node _btnClean_T_5 = and(_btnClean_T_3, _btnClean_T_4) @[Debounce.scala 43:61]
    node _btnClean_T_6 = or(_btnClean_T_2, _btnClean_T_5) @[Debounce.scala 43:46]
    node _btnClean_T_7 = bits(shiftReg, 1, 1) @[Debounce.scala 43:87]
    node _btnClean_T_8 = bits(shiftReg, 0, 0) @[Debounce.scala 43:101]
    node _btnClean_T_9 = and(_btnClean_T_7, _btnClean_T_8) @[Debounce.scala 43:91]
    node btnClean = or(_btnClean_T_6, _btnClean_T_9) @[Debounce.scala 43:76]
    reg risingEdge_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), risingEdge_REG) @[Debounce.scala 47:39]
    risingEdge_REG <= btnClean @[Debounce.scala 47:39]
    node _risingEdge_T = eq(risingEdge_REG, UInt<1>("h0")) @[Debounce.scala 47:31]
    node risingEdge = and(btnClean, _risingEdge_T) @[Debounce.scala 47:29]
    reg reg_wky: UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[Debounce.scala 51:20]
    when risingEdge : @[Debounce.scala 52:21]
    {
      node _reg_T = add(reg_wky, UInt<1>("h1")) @[Debounce.scala 53:16]
      node _reg_T_1 = tail(_reg_T, 1) @[Debounce.scala 53:16]
      reg_wky <= _reg_T_1 @[Debounce.scala 53:9]
    }
    io.led <= reg_wky @[Debounce.scala 57:10]

