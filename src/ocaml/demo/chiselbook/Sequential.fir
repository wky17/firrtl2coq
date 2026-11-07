circuit Sequential :
  module Sequential :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip d : UInt<4>, q : UInt<4>, flip d2 : UInt<4>, q2 : UInt<4>, flip d3 : UInt<4>, q3 : UInt<4>, flip ena : UInt<1>, q4 : UInt<4>, q5 : UInt<4>, q6 : UInt<4>, q7 : UInt<4>, flip riseIn : UInt<1>, riseOut : UInt<1>}

    reg q : UInt<4>, clock with :
      reset => (UInt<1>("h0"), q) @[Sequential.scala 23:18]
    q <= io.d @[Sequential.scala 23:18]
    io.q <= q @[Sequential.scala 25:8]
    reg delayReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), delayReg) @[Sequential.scala 29:21]
    delayReg <= io.d2 @[Sequential.scala 31:12]
    io.q2 <= delayReg @[Sequential.scala 33:9]
    reg valReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h0")) @[Sequential.scala 37:23]
    valReg <= io.d3 @[Sequential.scala 39:10]
    io.q3 <= valReg @[Sequential.scala 41:9]
    reg enableReg : UInt<4>, clock with :
      reset => (UInt<1>("h0"), enableReg) @[Sequential.scala 45:22]
    when io.ena : @[Sequential.scala 47:17]
    {
      enableReg <= io.d3 @[Sequential.scala 48:15]
    }
    io.q4 <= enableReg @[Sequential.scala 51:9]
    reg resetEnableReg : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h0")) @[Sequential.scala 54:31]
    when io.ena : @[Sequential.scala 56:17]
    {
      resetEnableReg <= io.d3 @[Sequential.scala 57:20]
    }
    io.q5 <= resetEnableReg @[Sequential.scala 60:9]
    reg enableReg2 : UInt<4>, clock with :
      reset => (UInt<1>("h0"), enableReg2) @[Reg.scala 19:16]
    when io.ena : @[Reg.scala 20:18]
    {
      enableReg2 <= io.d3 @[Reg.scala 20:22]
    }
    io.q6 <= enableReg2 @[Sequential.scala 65:9]
    reg resetEnableReg2 : UInt<4>, clock with :
      reset => (reset1, UInt<4>("h0")) @[Reg.scala 35:20]
    when io.ena : @[Reg.scala 36:18]
    {
      resetEnableReg2 <= io.d3 @[Reg.scala 36:22]
    }
    io.q7 <= resetEnableReg2 @[Sequential.scala 70:9]
    reg risingEdge_REG : UInt<1>, clock with :
      reset => (UInt<1>("h0"), risingEdge_REG) @[Sequential.scala 74:34]
    risingEdge_REG <= io.riseIn @[Sequential.scala 74:34]
    node _risingEdge_T = eq(risingEdge_REG, UInt<1>("h0")) @[Sequential.scala 74:26]
    node risingEdge = and(io.riseIn, _risingEdge_T) @[Sequential.scala 74:24]
    io.riseOut <= risingEdge @[Sequential.scala 76:14]

