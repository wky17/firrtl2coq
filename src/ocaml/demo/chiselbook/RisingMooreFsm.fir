circuit RisingMooreFsm :
  module RisingMooreFsm :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<1>, risingEdge : UInt<1>}

    reg stateReg : UInt<2>, clock with :
      reset => (reset1, UInt<1>("h0")) @[RisingMooreFsm.scala 17:25]
    node _T = asUInt(UInt<1>("h0")) @[RisingMooreFsm.scala 20:21]
    node _T_1 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
    node _T_2 = eq(_T, _T_1) @[RisingMooreFsm.scala 20:21]
    when _T_2 : @[RisingMooreFsm.scala 20:21]
    {
      when io.din : @[RisingMooreFsm.scala 22:20]
      {
        stateReg <= UInt<1>("h1") @[RisingMooreFsm.scala 23:18]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[RisingMooreFsm.scala 20:21]
      node _T_4 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
      node _T_5 = eq(_T_3, _T_4) @[RisingMooreFsm.scala 20:21]
      when _T_5 : @[RisingMooreFsm.scala 20:21]
      {
        when io.din : @[RisingMooreFsm.scala 27:20]
        {
          stateReg <= UInt<2>("h2") @[RisingMooreFsm.scala 28:18]
        }
        else :
        {
          stateReg <= UInt<1>("h0") @[RisingMooreFsm.scala 30:18]
      }
      }
      else :
      {
        node _T_6 = asUInt(UInt<2>("h2")) @[RisingMooreFsm.scala 20:21]
        node _T_7 = asUInt(stateReg) @[RisingMooreFsm.scala 20:21]
        node _T_8 = eq(_T_6, _T_7) @[RisingMooreFsm.scala 20:21]
        when _T_8 : @[RisingMooreFsm.scala 20:21]
        {
          node _T_9 = eq(io.din, UInt<1>("h0")) @[RisingMooreFsm.scala 34:12]
          when _T_9 : @[RisingMooreFsm.scala 34:21]
          {
            stateReg <= UInt<1>("h0") @[RisingMooreFsm.scala 35:18]
    }
    }
    }
    }
    node _io_risingEdge_T = eq(stateReg, UInt<1>("h1")) @[RisingMooreFsm.scala 41:29]
    io.risingEdge <= _io_risingEdge_T @[RisingMooreFsm.scala 41:17]

