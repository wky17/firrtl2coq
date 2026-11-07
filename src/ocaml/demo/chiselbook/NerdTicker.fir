circuit NerdTicker :
  module NerdTicker :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { tick : UInt<1>}

    reg cntReg : SInt<8>, clock with :
      reset => (reset1, asSInt(UInt<8>("h8"))) @[Ticker.scala 58:23]
    io.tick <= UInt<1>("h0") @[Ticker.scala 59:11]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Ticker.scala 61:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Ticker.scala 61:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Ticker.scala 61:20]
    cntReg <= _cntReg_T_2 @[Ticker.scala 61:10]
    node _T = bits(cntReg, 7, 7) @[Ticker.scala 62:14]
    when _T : @[Ticker.scala 62:19]
    {
      cntReg <= asSInt(UInt<8>("h8")) @[Ticker.scala 63:12]
      io.tick <= UInt<1>("h1") @[Ticker.scala 64:13]
 }


