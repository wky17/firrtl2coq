circuit DownTicker :
  module DownTicker :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { tick : UInt<1>}

    reg cntReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h9")) @[Ticker.scala 37:23]
    node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Ticker.scala 39:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 39:20]
    cntReg <= _cntReg_T_1 @[Ticker.scala 39:10]
    node _T = eq(cntReg, UInt<1>("h0")) @[Ticker.scala 40:15]
    when _T : @[Ticker.scala 40:24]
    {
      cntReg <= UInt<4>("h9") @[Ticker.scala 41:12]
    }
    node _io_tick_T = eq(cntReg, UInt<4>("h9")) @[Ticker.scala 44:21]
    io.tick <= _io_tick_T @[Ticker.scala 44:11]

