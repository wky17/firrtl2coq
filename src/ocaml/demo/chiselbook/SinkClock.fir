circuit SinkClock :
  module SinkClock :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip c : { data : UInt<32>, valid : UInt<1>}, errorCnt : UInt<8>}

    reg expectedCntReg : UInt<32>, clock with :
      reset => (reset1, UInt<32>("h0")) @[ClockDomains.scala 36:31]
    reg errCntReg : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[ClockDomains.scala 37:26]
    reg sampleReg : UInt<32>, clock with :
      reset => (reset1, UInt<32>("h0")) @[ClockDomains.scala 38:26]
    reg rising_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), rising_REG) @[ClockDomains.scala 40:37]
    rising_REG <= io.c.valid @[ClockDomains.scala 40:37]
    node _rising_T = eq(rising_REG, UInt<1>("h0")) @[ClockDomains.scala 40:29]
    node rising = and(io.c.valid, _rising_T) @[ClockDomains.scala 40:27]
    when rising : @[ClockDomains.scala 42:17]
    {
      node _T = neq(expectedCntReg, io.c.data) @[ClockDomains.scala 43:26]
      when _T : @[ClockDomains.scala 43:41]
      {
        node _errCntReg_T = add(errCntReg, UInt<1>("h1")) @[ClockDomains.scala 44:30]
        node _errCntReg_T_1 = tail(_errCntReg_T, 1) @[ClockDomains.scala 44:30]
        errCntReg <= _errCntReg_T_1 @[ClockDomains.scala 44:17]
      }
      sampleReg <= io.c.data @[ClockDomains.scala 46:15]
      node _expectedCntReg_T = add(expectedCntReg, UInt<1>("h1")) @[ClockDomains.scala 47:38]
      node _expectedCntReg_T_1 = tail(_expectedCntReg_T, 1) @[ClockDomains.scala 47:38]
      expectedCntReg <= _expectedCntReg_T_1 @[ClockDomains.scala 47:20]
    }
    io.errorCnt <= errCntReg @[ClockDomains.scala 50:15]

