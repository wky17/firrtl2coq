circuit Flasher :
  module Flasher :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip start : UInt<1>, light : UInt<1>}

    node start = bits(io.start, 0, 0) @[Flasher.scala 13:24]
    reg stateReg : UInt<3>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[Flasher.scala 22:25]
    wire light : UInt<1> @[Flasher.scala 24:26]
    light <= UInt<1>("h0") @[Flasher.scala 24:26]
    wire timerLoad : UInt<1> @[Flasher.scala 27:30]
    timerLoad <= UInt<1>("h0") @[Flasher.scala 27:30]
    wire timerSelect : UInt<1> @[Flasher.scala 28:32]
    timerSelect <= UInt<1>("h1") @[Flasher.scala 28:32]
    wire timerDone : UInt<1> @[Flasher.scala 29:23]
    timerLoad <= timerDone @[Flasher.scala 31:13]
    node _T = asUInt(UInt<1>("h0")) @[Flasher.scala 34:20]
    node _T_1 = asUInt(stateReg) @[Flasher.scala 34:20]
    node _T_2 = eq(_T, _T_1) @[Flasher.scala 34:20]
    when _T_2 : @[Flasher.scala 34:20]
    {
      timerLoad <= UInt<1>("h1") @[Flasher.scala 36:17]
      timerSelect <= UInt<1>("h1") @[Flasher.scala 37:19]
      when start : @[Flasher.scala 38:20]
      {
        stateReg <= UInt<1>("h1") @[Flasher.scala 38:31]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[Flasher.scala 34:20]
      node _T_4 = asUInt(stateReg) @[Flasher.scala 34:20]
      node _T_5 = eq(_T_3, _T_4) @[Flasher.scala 34:20]
      when _T_5 : @[Flasher.scala 34:20]
      {
        timerSelect <= UInt<1>("h0") @[Flasher.scala 41:19]
        light <= UInt<1>("h1") @[Flasher.scala 42:13]
        when timerDone : @[Flasher.scala 43:24]
        {
          stateReg <= UInt<2>("h2") @[Flasher.scala 43:35]
      }
      }
      else :
      {
        node _T_6 = asUInt(UInt<2>("h2")) @[Flasher.scala 34:20]
        node _T_7 = asUInt(stateReg) @[Flasher.scala 34:20]
        node _T_8 = eq(_T_6, _T_7) @[Flasher.scala 34:20]
        when _T_8 : @[Flasher.scala 34:20]
        {
          when timerDone : @[Flasher.scala 46:24]
          {
            stateReg <= UInt<2>("h3") @[Flasher.scala 46:35]
        }
        }
        else :
        {
          node _T_9 = asUInt(UInt<2>("h3")) @[Flasher.scala 34:20]
          node _T_10 = asUInt(stateReg) @[Flasher.scala 34:20]
          node _T_11 = eq(_T_9, _T_10) @[Flasher.scala 34:20]
          when _T_11 : @[Flasher.scala 34:20]
          {
            timerSelect <= UInt<1>("h0") @[Flasher.scala 49:19]
            light <= UInt<1>("h1") @[Flasher.scala 50:13]
            when timerDone : @[Flasher.scala 51:24]
            {
              stateReg <= UInt<3>("h4") @[Flasher.scala 51:35]
          }
          }
          else :
          {
            node _T_12 = asUInt(UInt<3>("h4")) @[Flasher.scala 34:20]
            node _T_13 = asUInt(stateReg) @[Flasher.scala 34:20]
            node _T_14 = eq(_T_12, _T_13) @[Flasher.scala 34:20]
            when _T_14 : @[Flasher.scala 34:20]
            {
              when timerDone : @[Flasher.scala 54:24]
              {
                stateReg <= UInt<3>("h5") @[Flasher.scala 54:35]
            }
            }
            else :
            {
              node _T_15 = asUInt(UInt<3>("h5")) @[Flasher.scala 34:20]
              node _T_16 = asUInt(stateReg) @[Flasher.scala 34:20]
              node _T_17 = eq(_T_15, _T_16) @[Flasher.scala 34:20]
              when _T_17 : @[Flasher.scala 34:20]
              {
                timerSelect <= UInt<1>("h0") @[Flasher.scala 57:19]
                light <= UInt<1>("h1") @[Flasher.scala 58:13]
                when timerDone : @[Flasher.scala 59:24]
                {
                  stateReg <= UInt<1>("h0") @[Flasher.scala 59:35]
    }
    }
    }
    }
    }
    }
    }
    reg timerReg : UInt<3>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[Flasher.scala 65:25]
    node _timerDone_T = eq(timerReg, UInt<1>("h0")) @[Flasher.scala 66:25]
    timerDone <= _timerDone_T @[Flasher.scala 66:13]
    node _T_18 = eq(timerDone, UInt<1>("h0")) @[Flasher.scala 69:8]
    when _T_18 : @[Flasher.scala 69:20]
    {
      node _timerReg_T = sub(timerReg, UInt<1>("h1")) @[Flasher.scala 70:26]
      node _timerReg_T_1 = tail(_timerReg_T, 1) @[Flasher.scala 70:26]
      timerReg <= _timerReg_T_1 @[Flasher.scala 70:14]
    }
    when timerLoad : @[Flasher.scala 72:20]
    {
      when timerSelect : @[Flasher.scala 73:24]
      {
        timerReg <= UInt<3>("h5") @[Flasher.scala 74:16]
      }
      else :
      {
        timerReg <= UInt<2>("h3") @[Flasher.scala 76:16]
    }
    }
    io.light <= light @[Flasher.scala 81:12]

