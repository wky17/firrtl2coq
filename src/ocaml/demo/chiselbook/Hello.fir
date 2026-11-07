circuit Hello :
  module Hello :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { led : UInt<1>}

    reg cntReg : UInt<32>, clock with :
      reset => (reset1, UInt<32>("h0")) @[Hello.scala 26:23]
    reg blkReg : UInt<1>, clock with :
      reset => (reset1, UInt<1>("h0")) @[Hello.scala 27:23]
    node _cntReg_T = add(cntReg, UInt<1>("h1")) @[Hello.scala 29:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Hello.scala 29:20]
    cntReg <= _cntReg_T_1 @[Hello.scala 29:10]
    node _T = eq(cntReg, UInt<25>("h17d783f")) @[Hello.scala 30:15]
    when _T : @[Hello.scala 30:28]
    {
      cntReg <= UInt<1>("h0") @[Hello.scala 31:12]
      node _blkReg_T = not(blkReg) @[Hello.scala 32:15]
      blkReg <= _blkReg_T @[Hello.scala 32:12]
    }
    io.led <= blkReg @[Hello.scala 34:10]

