circuit PopulationCount :
  module PopCountFSM :
    input clock: Clock
    input reset_wky: Reset
    output io : { flip dinValid : UInt<1>, dinReady : UInt<1>, popCntValid : UInt<1>, flip popCntReady : UInt<1>, load : UInt<1>, flip done : UInt<1>}

    reg stateReg : UInt<2>, clock with :
      reset => (reset_wky, UInt<1>("h0")) @[PopulationCount.scala 19:25]
    io.load <= UInt<1>("h0") @[PopulationCount.scala 20:11]
    io.dinReady <= UInt<1>("h0") @[PopulationCount.scala 21:15]
    io.popCntValid <= UInt<1>("h0") @[PopulationCount.scala 22:18]
    node _T = asUInt(UInt<1>("h0")) @[PopulationCount.scala 24:20]
    node _T_1 = asUInt(stateReg) @[PopulationCount.scala 24:20]
    node _T_2 = eq(_T, _T_1) @[PopulationCount.scala 24:20]
    when _T_2 : @[PopulationCount.scala 24:20]
    {
      io.dinReady <= UInt<1>("h1") @[PopulationCount.scala 26:19]
      when io.dinValid : @[PopulationCount.scala 27:25]
      {
        io.load <= UInt<1>("h1") @[PopulationCount.scala 28:17]
        stateReg <= UInt<1>("h1") @[PopulationCount.scala 29:18]
    }
    }
    else :
    {
      node _T_3 = asUInt(UInt<1>("h1")) @[PopulationCount.scala 24:20]
      node _T_4 = asUInt(stateReg) @[PopulationCount.scala 24:20]
      node _T_5 = eq(_T_3, _T_4) @[PopulationCount.scala 24:20]
      when _T_5 : @[PopulationCount.scala 24:20]
      {
        when io.done : @[PopulationCount.scala 33:21]
        {
          stateReg <= UInt<2>("h2") @[PopulationCount.scala 34:18]
      }
      }
      else :
      {
        node _T_6 = asUInt(UInt<2>("h2")) @[PopulationCount.scala 24:20]
        node _T_7 = asUInt(stateReg) @[PopulationCount.scala 24:20]
        node _T_8 = eq(_T_6, _T_7) @[PopulationCount.scala 24:20]
        when _T_8 : @[PopulationCount.scala 24:20]
        {
          io.popCntValid <= UInt<1>("h1") @[PopulationCount.scala 38:22]
          when io.popCntReady : @[PopulationCount.scala 39:28]
          {
            stateReg <= UInt<1>("h0") @[PopulationCount.scala 40:18]
 }
 }
 }
 }


  module PopCountDataPath :
    input clock: Clock
    input reset_wky: Reset
    output io : { flip din : UInt<8>, flip load : UInt<1>, popCnt : UInt<4>, done : UInt<1>}

    reg dataReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[PopulationCount.scala 54:24]
    reg popCntReg : UInt<8>, clock with :
      reset => (reset_wky, UInt<8>("h0")) @[PopulationCount.scala 55:26]
    reg counterReg : UInt<4>, clock with :
      reset => (reset_wky, UInt<4>("h0")) @[PopulationCount.scala 56:26]
    node _dataReg_T = bits(dataReg, 7, 1) @[PopulationCount.scala 58:28]
    node _dataReg_T_1 = cat(UInt<1>("h0"), _dataReg_T) @[PopulationCount.scala 58:18]
    dataReg <= _dataReg_T_1 @[PopulationCount.scala 58:11]
    node _popCntReg_T = bits(dataReg, 0, 0) @[PopulationCount.scala 59:35]
    node _popCntReg_T_1 = add(popCntReg, _popCntReg_T) @[PopulationCount.scala 59:26]
    node _popCntReg_T_2 = tail(_popCntReg_T_1, 1) @[PopulationCount.scala 59:26]
    popCntReg <= _popCntReg_T_2 @[PopulationCount.scala 59:13]
    node done = eq(counterReg, UInt<1>("h0")) @[PopulationCount.scala 61:25]
    node _T = eq(done, UInt<1>("h0")) @[PopulationCount.scala 62:9]
    when _T : @[PopulationCount.scala 62:16]
    {
      node _counterReg_T = sub(counterReg, UInt<1>("h1")) @[PopulationCount.scala 63:30]
      node _counterReg_T_1 = tail(_counterReg_T, 1) @[PopulationCount.scala 63:30]
      counterReg <= _counterReg_T_1 @[PopulationCount.scala 63:16]
    }
    when io.load : @[PopulationCount.scala 66:17]
    {
      dataReg <= io.din @[PopulationCount.scala 67:13]
      popCntReg <= UInt<1>("h0") @[PopulationCount.scala 68:15]
      counterReg <= UInt<4>("h8") @[PopulationCount.scala 69:16]
    }
    node _T_1 = asUInt(reset_wky) @[PopulationCount.scala 73:9]
    node _T_2 = eq(_T_1, UInt<1>("h0")) @[PopulationCount.scala 73:9]
    io.popCnt <= popCntReg @[PopulationCount.scala 75:13]
    io.done <= done @[PopulationCount.scala 76:11]

  module PopulationCount :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip dinValid : UInt<1>, dinReady : UInt<1>, flip din : UInt<8>, popCntValid : UInt<1>, flip popCntReady : UInt<1>, popCnt : UInt<4>}

    inst fsm aof PopCountFSM @[PopulationCount.scala 92:19]
    fsm.clock <= clock
    fsm.reset_wky <= reset_wky
    inst data aof PopCountDataPath @[PopulationCount.scala 93:20]
    data.clock <= clock
    data.reset_wky <= reset_wky
    fsm.io.dinValid <= io.dinValid @[PopulationCount.scala 95:19]
    io.dinReady <= fsm.io.dinReady @[PopulationCount.scala 96:15]
    io.popCntValid <= fsm.io.popCntValid @[PopulationCount.scala 97:18]
    fsm.io.popCntReady <= io.popCntReady @[PopulationCount.scala 98:22]
    data.io.din <= io.din @[PopulationCount.scala 100:15]
    io.popCnt <= data.io.popCnt @[PopulationCount.scala 101:13]
    data.io.load <= fsm.io.load @[PopulationCount.scala 102:16]
    fsm.io.done <= data.io.done @[PopulationCount.scala 103:15]

