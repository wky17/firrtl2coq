circuit NerdCounter :
  module NerdCounter :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { cnt : UInt<8>, tick : UInt<1>}

    reg cntReg : SInt<8>, clock with :
      reset => (reset1, asSInt(UInt<8>("h8"))) @[Counter.scala 99:23]
    io.tick <= UInt<1>("h0") @[Counter.scala 100:11]
    node _cntReg_T = sub(cntReg, asSInt(UInt<2>("h1"))) @[Counter.scala 102:20]
    node _cntReg_T_1 = tail(_cntReg_T, 1) @[Counter.scala 102:20]
    node _cntReg_T_2 = asSInt(_cntReg_T_1) @[Counter.scala 102:20]
    cntReg <= _cntReg_T_2 @[Counter.scala 102:10]
    node _T = bits(cntReg, 7, 7) @[Counter.scala 103:14]
    when _T : @[Counter.scala 103:19]
    {
      cntReg <= asSInt(UInt<8>("h8")) @[Counter.scala 104:12]
      io.tick <= UInt<1>("h1") @[Counter.scala 105:13]
    }
    node _io_cnt_T = asUInt(cntReg) @[Counter.scala 109:20]
    io.cnt <= _io_cnt_T @[Counter.scala 109:10]

