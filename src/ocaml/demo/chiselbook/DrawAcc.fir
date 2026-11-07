circuit DrawAcc :
  module DrawAcc :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip din : UInt<8>, flip sel : UInt<3>, dout : UInt<8>}

    reg regAcc : UInt<8>, clock with :
      reset => (reset1, UInt<8>("h0")) @[drawing.scala 17:23]
    node _T = eq(UInt<1>("h0"), io.sel) @[drawing.scala 19:15]
    when _T : @[drawing.scala 19:15]
    {
      regAcc <= regAcc @[drawing.scala 20:22]
    }
    else :
    {
      node _T_1 = eq(UInt<1>("h1"), io.sel) @[drawing.scala 19:15]
      when _T_1 : @[drawing.scala 19:15]
      {
        regAcc <= UInt<1>("h0") @[drawing.scala 21:22]
      }
      else :
      {
        node _T_2 = eq(UInt<2>("h2"), io.sel) @[drawing.scala 19:15]
        when _T_2 : @[drawing.scala 19:15]
        {
          node _regAcc_T = add(regAcc, io.din) @[drawing.scala 22:32]
          node _regAcc_T_1 = tail(_regAcc_T, 1) @[drawing.scala 22:32]
          regAcc <= _regAcc_T_1 @[drawing.scala 22:22]
        }
        else :
        {
          node _T_3 = eq(UInt<2>("h3"), io.sel) @[drawing.scala 19:15]
          when _T_3 : @[drawing.scala 19:15]
          {
            node _regAcc_T_2 = sub(regAcc, io.din) @[drawing.scala 23:32]
            node _regAcc_T_3 = tail(_regAcc_T_2, 1) @[drawing.scala 23:32]
            regAcc <= _regAcc_T_3 @[drawing.scala 23:22]
    }
    }
    }
    }
    io.dout <= regAcc @[drawing.scala 27:11]

