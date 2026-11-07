circuit UpTicker :
  module UpTicker :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { tick : UInt<1>}

    reg cntReg : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[Ticker.scala 16:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Ticker.scala 18:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 18:20]
    cntReg <= _cntReg_T_1 @[Ticker.scala 18:10]
    node tick = eq(cntReg, UInt<4>("h9")) @[Ticker.scala 19:21]
    when tick : @[Ticker.scala 20:14]
    {
      cntReg <= UInt<1>("h0") @[Ticker.scala 21:12]
    }
    io.tick <= tick @[Ticker.scala 24:11]

