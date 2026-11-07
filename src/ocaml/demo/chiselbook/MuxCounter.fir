circuit MuxCounter :
  module MuxCounter :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 46:23]
    node _cntReg_T = eq(cntReg, UInt<4>("h9")) @[Counter.scala 48:24]
    node _cntReg_T_1 = add(cntReg, UInt<1>("h1")) @[Counter.scala 48:43]
    node _cntReg_T_2 = tail(_cntReg_T_1, 1) @[Counter.scala 48:43]
    node _cntReg_T_3 = mux(_cntReg_T, UInt<1>("h0"), _cntReg_T_2) @[Counter.scala 48:16]
    cntReg <= _cntReg_T_3 @[Counter.scala 48:10]
    node _io_tick_T = eq(cntReg, UInt<4>("h9")) @[Counter.scala 51:21]
    io.tick <= _io_tick_T @[Counter.scala 51:11]
    io.cnt <= cntReg @[Counter.scala 52:10]

