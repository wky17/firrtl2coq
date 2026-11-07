circuit SimpleFsm :
  module SimpleFsm :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip badEvent : UInt<1>, flip clear : UInt<1>, ringBell : UInt<1>}

    reg stateReg : UInt<2>, clock with :
      reset => (reset1, UInt<1>("h0")) @[SimpleFsm.scala 18:25]
    node _T = asUInt(UInt<1>("h0")) @[SimpleFsm.scala 21:21]
    node _T_1 = asUInt(stateReg) @[SimpleFsm.scala 21:21]
    node _T_2 = eq(_T, _T_1) @[SimpleFsm.scala 21:21]
    when _T_2 : @[SimpleFsm.scala 21:21]
    {
      when io.badEvent : @[SimpleFsm.scala 23:25]
      {
        stateReg <= UInt<1>("h1") @[SimpleFsm.scala 24:18]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[SimpleFsm.scala 21:21]
      node _T_4 = asUInt(stateReg) @[SimpleFsm.scala 21:21]
      node _T_5 = eq(_T_3, _T_4) @[SimpleFsm.scala 21:21]
      when _T_5 : @[SimpleFsm.scala 21:21]
      {
        when io.badEvent : @[SimpleFsm.scala 28:25]
        {
          stateReg <= UInt<2>("h2") @[SimpleFsm.scala 29:18]
        }
        else :
        {
          when io.clear : @[SimpleFsm.scala 30:29]
          {
            stateReg <= UInt<1>("h0") @[SimpleFsm.scala 31:18]
      }
      }
      }
      else :
      {
        node _T_6 = asUInt(UInt<2>("h2")) @[SimpleFsm.scala 21:21]
        node _T_7 = asUInt(stateReg) @[SimpleFsm.scala 21:21]
        node _T_8 = eq(_T_6, _T_7) @[SimpleFsm.scala 21:21]
        when _T_8 : @[SimpleFsm.scala 21:21]
        {
          when io.clear : @[SimpleFsm.scala 35:23]
          {
            stateReg <= UInt<1>("h0") @[SimpleFsm.scala 36:18]
    }
    }
    }
    }
    node _io_ringBell_T = eq(stateReg, UInt<2>("h2")) @[SimpleFsm.scala 41:27]
    io.ringBell <= _io_ringBell_T @[SimpleFsm.scala 41:15]

