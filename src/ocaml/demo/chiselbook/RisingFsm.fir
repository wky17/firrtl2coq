circuit RisingFsm :
  module RisingFsm :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<1>, risingEdge : UInt<1>}

    reg stateReg : UInt<1>, clock with :
      reset => (reset1, UInt<1>("h0")) @[RisingFsm.scala 18:25]
    io.risingEdge <= UInt<1>("h0") @[RisingFsm.scala 21:17]
    node _T = asUInt(UInt<1>("h0")) @[RisingFsm.scala 24:21]
    node _T_1 = asUInt(stateReg) @[RisingFsm.scala 24:21]
    node _T_2 = eq(_T, _T_1) @[RisingFsm.scala 24:21]
    when _T_2 : @[RisingFsm.scala 24:21]
    {
      when io.din : @[RisingFsm.scala 26:20]
      {
        stateReg <= UInt<1>("h1") @[RisingFsm.scala 27:18]
        io.risingEdge <= UInt<1>("h1") @[RisingFsm.scala 28:23]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[RisingFsm.scala 24:21]
      node _T_4 = asUInt(stateReg) @[RisingFsm.scala 24:21]
      node _T_5 = eq(_T_3, _T_4) @[RisingFsm.scala 24:21]
      when _T_5 : @[RisingFsm.scala 24:21]
      {
        node _T_6 = eq(io.din, UInt<1>("h0")) @[RisingFsm.scala 32:12]
        when _T_6 : @[RisingFsm.scala 32:21]
        {
          stateReg <= UInt<1>("h0") @[RisingFsm.scala 33:18]
 }
 }
 }


