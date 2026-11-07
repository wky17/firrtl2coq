circuit Arbiter3Direct :
  module Arbiter3Direct :
    input clock_wky: Clock
    input reset1 : UInt<1>
    output io : { flip request : UInt<3>, grant : UInt<3>}

    wire grant : UInt<3> @[arbiter.scala 40:26]
    grant <= UInt<3>("h0") @[arbiter.scala 40:26]
    node _T = eq(UInt<1>("h0"), io.request) @[arbiter.scala 41:20]
    when _T : @[arbiter.scala 41:20]
    {
      grant <= UInt<1>("h0") @[arbiter.scala 42:27]
    }
    else :
    {
      node _T_1 = eq(UInt<1>("h1"), io.request) @[arbiter.scala 41:20]
      when _T_1 : @[arbiter.scala 41:20]
      {
        grant <= UInt<1>("h1") @[arbiter.scala 43:27]
      }
      else :
      {
        node _T_2 = eq(UInt<2>("h2"), io.request) @[arbiter.scala 41:20]
        when _T_2 : @[arbiter.scala 41:20]
        {
          grant <= UInt<2>("h2") @[arbiter.scala 44:27]
        }
        else :
        {
          node _T_3 = eq(UInt<2>("h3"), io.request) @[arbiter.scala 41:20]
          when _T_3 : @[arbiter.scala 41:20]
          {
            grant <= UInt<1>("h1") @[arbiter.scala 45:27]
          }
          else :
          {
            node _T_4 = eq(UInt<3>("h4"), io.request) @[arbiter.scala 41:20]
            when _T_4 : @[arbiter.scala 41:20]
            {
              grant <= UInt<3>("h4") @[arbiter.scala 46:27]
            }
            else :
            {
              node _T_5 = eq(UInt<3>("h5"), io.request) @[arbiter.scala 41:20]
              when _T_5 : @[arbiter.scala 41:20]
              {
                grant <= UInt<1>("h1") @[arbiter.scala 47:27]
              }
              else :
              {
                node _T_6 = eq(UInt<3>("h6"), io.request) @[arbiter.scala 41:20]
                when _T_6 : @[arbiter.scala 41:20]
                {
                  grant <= UInt<2>("h2") @[arbiter.scala 48:27]
                }
                else :
                {
                  node _T_7 = eq(UInt<3>("h7"), io.request) @[arbiter.scala 41:20]
                  when _T_7 : @[arbiter.scala 41:20]
                  {
                    grant <= UInt<1>("h1") @[arbiter.scala 49:27]
    }
    }
    }
    }
    }
    }
    }
    }
    io.grant <= grant @[arbiter.scala 52:12]

