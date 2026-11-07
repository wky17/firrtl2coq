circuit WhenCounter :
  module WhenCounter :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Counter.scala 29:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Counter.scala 31:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 31:20]
    cntReg <= _cntReg_T_1 @[Counter.scala 31:10]
    node _T = eq(cntReg, UInt<4>("h9")) @[Counter.scala 32:15]
    when _T : @[Counter.scala 32:22]
    {
      cntReg <= UInt<1>("h0") @[Counter.scala 33:12]
    }
    node _io_tick_T = eq(cntReg, UInt<4>("h9")) @[Counter.scala 37:21]
    io.tick <= _io_tick_T @[Counter.scala 37:11]
    io.cnt <= cntReg @[Counter.scala 38:10]

