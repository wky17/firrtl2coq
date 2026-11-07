circuit Flasher2 :
  module Flasher2 :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip start : UInt<1>, light : UInt<1>}

    node start = bits(io.start, 0, 0) @[Flasher.scala 90:24]
    reg stateReg : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[Flasher.scala 98:25]
    wire light : UInt<1> @[Flasher.scala 100:26]
    light <= UInt<1>("h0") @[Flasher.scala 100:26]
    wire timerLoad : UInt<1> @[Flasher.scala 103:30]
    timerLoad <= UInt<1>("h0") @[Flasher.scala 103:30]
    wire timerSelect : UInt<1> @[Flasher.scala 104:32]
    timerSelect <= UInt<1>("h1") @[Flasher.scala 104:32]
    wire timerDone : UInt<1> @[Flasher.scala 105:23]
    wire cntLoad : UInt<1> @[Flasher.scala 107:28]
    cntLoad <= UInt<1>("h0") @[Flasher.scala 107:28]
    wire cntDecr : UInt<1> @[Flasher.scala 108:28]
    cntDecr <= UInt<1>("h0") @[Flasher.scala 108:28]
    wire cntDone : UInt<1> @[Flasher.scala 109:21]
    timerLoad <= timerDone @[Flasher.scala 111:13]
    node _T = asUInt(UInt<1>("h0")) @[Flasher.scala 113:20]
    node _T_1 = asUInt(stateReg) @[Flasher.scala 113:20]
    node _T_2 = eq(_T, _T_1) @[Flasher.scala 113:20]
    when _T_2 : @[Flasher.scala 113:20]
    {
      timerLoad <= UInt<1>("h1") @[Flasher.scala 115:17]
      timerSelect <= UInt<1>("h1") @[Flasher.scala 116:19]
      cntLoad <= UInt<1>("h1") @[Flasher.scala 117:15]
      when start : @[Flasher.scala 118:20]
      {
        stateReg <= UInt<1>("h1") @[Flasher.scala 118:31]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[Flasher.scala 113:20]
      node _T_4 = asUInt(stateReg) @[Flasher.scala 113:20]
      node _T_5 = eq(_T_3, _T_4) @[Flasher.scala 113:20]
      when _T_5 : @[Flasher.scala 113:20]
      {
        timerSelect <= UInt<1>("h0") @[Flasher.scala 121:19]
        light <= UInt<1>("h1") @[Flasher.scala 122:13]
        node _T_6 = eq(cntDone, UInt<1>("h0")) @[Flasher.scala 123:25]
        node _T_7 = and(timerDone, _T_6) @[Flasher.scala 123:23]
        when _T_7 : @[Flasher.scala 123:35]
        {
          stateReg <= UInt<2>("h2") @[Flasher.scala 123:46]
        }
        node _T_8 = and(timerDone, cntDone) @[Flasher.scala 124:23]
        when _T_8 : @[Flasher.scala 124:34]
        {
          stateReg <= UInt<1>("h0") @[Flasher.scala 124:45]
      }
      }
      else :
      {
        node _T_9 = asUInt(UInt<2>("h2")) @[Flasher.scala 113:20]
        node _T_10 = asUInt(stateReg) @[Flasher.scala 113:20]
        node _T_11 = eq(_T_9, _T_10) @[Flasher.scala 113:20]
        when _T_11 : @[Flasher.scala 113:20]
        {
          cntDecr <= timerDone @[Flasher.scala 127:15]
          when timerDone : @[Flasher.scala 128:24]
          {
            stateReg <= UInt<1>("h1") @[Flasher.scala 128:35]
    }
    }
    }
    }
    reg cntReg : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[Flasher.scala 134:23]
    node _cntDone_T = eq(cntReg, UInt<1>("h0")) @[Flasher.scala 135:21]
    cntDone <= _cntDone_T @[Flasher.scala 135:11]
    when cntLoad : @[Flasher.scala 138:17]
    {
      cntReg <= UInt<2>("h2") @[Flasher.scala 138:26]
    }
    when cntDecr : @[Flasher.scala 139:17]
    {
      node _cntReg_T = sub(cntReg, UInt<1>("h1")) @[Flasher.scala 139:36]
      node _cntReg_T_1 = tail(_cntReg_T, 1) @[Flasher.scala 139:36]
      cntReg <= _cntReg_T_1 @[Flasher.scala 139:26]
    }
    reg timerReg : UInt<3>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[Flasher.scala 142:25]
    node _timerDone_T = eq(timerReg, UInt<1>("h0")) @[Flasher.scala 143:25]
    timerDone <= _timerDone_T @[Flasher.scala 143:13]
    node _T_12 = eq(timerDone, UInt<1>("h0")) @[Flasher.scala 146:8]
    when _T_12 : @[Flasher.scala 146:20]
    {
      node _timerReg_T = sub(timerReg, UInt<1>("h1")) @[Flasher.scala 147:26]
      node _timerReg_T_1 = tail(_timerReg_T, 1) @[Flasher.scala 147:26]
      timerReg <= _timerReg_T_1 @[Flasher.scala 147:14]
    }
    when timerLoad : @[Flasher.scala 149:20]
    {
      when timerSelect : @[Flasher.scala 150:24]
      {
        timerReg <= UInt<3>("h5") @[Flasher.scala 151:16]
      }
      else :
      {
        timerReg <= UInt<2>("h3") @[Flasher.scala 153:16]
    }
    }
    io.light <= light @[Flasher.scala 157:12]

