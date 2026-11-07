circuit SourceClock :
  module SourceClock :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { c : { data : UInt<32>, valid : UInt<1>}}

    reg valid : UInt<1>, clock with :
      reset => (reset1, UInt<1>("h0")) @[ClockDomains.scala 12:22]
    reg cntReg : UInt<32>, clock with :
      reset => (reset1, UInt<32>("h0")) @[ClockDomains.scala 13:23]
    reg xReg : UInt<2>, clock with :
      reset => (reset1, UInt<2>("h0")) @[ClockDomains.scala 14:21]
    node _xReg_T = add(xReg, UInt<1>("h1")) @[ClockDomains.scala 15:16]
    node _xReg_T_1 = tail(_xReg_T, 1) @[ClockDomains.scala 15:16]
    xReg <= _xReg_T_1 @[ClockDomains.scala 15:8]
    node _valid_T = bits(xReg, 1, 1) @[ClockDomains.scala 17:16]
    valid <= _valid_T @[ClockDomains.scala 17:9]
    node _falling_T = eq(valid, UInt<1>("h0")) @[ClockDomains.scala 18:17]
    reg falling_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), falling_REG) @[ClockDomains.scala 18:33]
    falling_REG <= valid @[ClockDomains.scala 18:33]
    node falling = and(_falling_T, falling_REG) @[ClockDomains.scala 18:24]
    when falling : @[ClockDomains.scala 19:18]
    {
      node _cntReg_T = add(cntReg, UInt<1>("h1")) @[ClockDomains.scala 20:22]
      node _cntReg_T_1 = tail(_cntReg_T, 1) @[ClockDomains.scala 20:22]
      cntReg <= _cntReg_T_1 @[ClockDomains.scala 20:12]
    }
    io.c.valid <= valid @[ClockDomains.scala 22:14]
    io.c.data <= cntReg @[ClockDomains.scala 23:13]

