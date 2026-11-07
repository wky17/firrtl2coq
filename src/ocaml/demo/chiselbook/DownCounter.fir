circuit DownCounter :
  module DownCounter :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h9")) @[Counter.scala 60:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Counter.scala 62:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 62:20]
    cntReg <= _cntReg_T_1 @[Counter.scala 62:10]
    node _T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 63:15]
    when _T : @[Counter.scala 63:24]
    {
      cntReg <= UInt<4>("h9") @[Counter.scala 64:12]
    }
    node _io_tick_T = eq(cntReg, UInt<1>("h0")) @[Counter.scala 68:21]
    io.tick <= _io_tick_T @[Counter.scala 68:11]
    io.cnt <= cntReg @[Counter.scala 69:10]

