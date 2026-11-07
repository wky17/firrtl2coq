circuit Conditional :
  module Conditional :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip condition : UInt<1>, result : UInt<4>}

    node c1 = eq(io.condition, UInt<1>("h0")) @[Snippets.scala 82:12]
    node c2 = eq(io.condition, UInt<1>("h0")) @[Snippets.scala 83:12]
    wire v : UInt @[Snippets.scala 85:15]
    v <= UInt<3>("h5") @[Snippets.scala 87:5]
    when io.condition : @[Snippets.scala 88:20]
    {
      v <= UInt<1>("h0") @[Snippets.scala 89:7]
    }
    when c1 : @[Snippets.scala 92:13]
    {
      v <= UInt<1>("h1") @[Snippets.scala 92:17]
    }
    when c2 : @[Snippets.scala 93:13]
    {
      v <= UInt<2>("h2") @[Snippets.scala 93:17]
    }
    when c1 : @[Snippets.scala 95:13]
    {
      v <= UInt<1>("h1") @[Snippets.scala 95:17]
    }
    else :
    {
      when c2 : @[Snippets.scala 96:20]
      {
        v <= UInt<2>("h2") @[Snippets.scala 96:24]
      }
      else :
      {
        v <= UInt<2>("h3") @[Snippets.scala 97:20]
    }
    }
    io.result <= v @[Snippets.scala 99:13]

