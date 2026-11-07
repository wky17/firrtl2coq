circuit DrawMux6 :
  module DrawMux6 :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip sel : UInt<3>, dout : UInt<8>}

    wire dout : UInt @[drawing.scala 43:25]
    dout <= UInt<1>("h0") @[drawing.scala 43:25]
    node _T = eq(UInt<1>("h0"), io.sel) @[drawing.scala 45:15]
    when _T : @[drawing.scala 45:15]
    {
      dout <= UInt<1>("h0") @[drawing.scala 46:20]
    }
    else :
    {
      node _T_1 = eq(UInt<1>("h1"), io.sel) @[drawing.scala 45:15]
      when _T_1 : @[drawing.scala 45:15]
      {
        dout <= UInt<4>("hb") @[drawing.scala 47:20]
      }
      else :
      {
        node _T_2 = eq(UInt<2>("h2"), io.sel) @[drawing.scala 45:15]
        when _T_2 : @[drawing.scala 45:15]
        {
          dout <= UInt<5>("h16") @[drawing.scala 48:20]
        }
        else :
        {
          node _T_3 = eq(UInt<2>("h3"), io.sel) @[drawing.scala 45:15]
          when _T_3 : @[drawing.scala 45:15]
          {
            dout <= UInt<6>("h21") @[drawing.scala 49:20]
          }
          else :
          {
            node _T_4 = eq(UInt<3>("h4"), io.sel) @[drawing.scala 45:15]
            when _T_4 : @[drawing.scala 45:15]
            {
              dout <= UInt<6>("h2c") @[drawing.scala 50:20]
            }
            else :
            {
              node _T_5 = eq(UInt<3>("h5"), io.sel) @[drawing.scala 45:15]
              when _T_5 : @[drawing.scala 45:15]
              {
                dout <= UInt<6>("h37") @[drawing.scala 51:20]
    }
    }
    }
    }
    }
    }
    io.dout <= dout @[drawing.scala 55:11]

