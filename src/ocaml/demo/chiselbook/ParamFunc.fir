circuit ParamFunc :
  module ParamFunc :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip selA : UInt<1>, resA : UInt<5>, flip selB : UInt<1>, resB : { d : UInt<10>, b : UInt<1>}}

    wire resA : UInt @[ParamFunc.scala 22:26]
    resA <= UInt<4>("ha") @[ParamFunc.scala 22:26]
    when io.selA : @[ParamFunc.scala 23:16]
    {
      resA <= UInt<3>("h5") @[ParamFunc.scala 24:11]
    }
    wire tVal : { d : UInt<10>, b : UInt<1>} @[ParamFunc.scala 57:18]
    tVal.b <= UInt<1>("h1") @[ParamFunc.scala 58:10]
    tVal.d <= UInt<6>("h2a") @[ParamFunc.scala 59:10]
    wire fVal : { d : UInt<10>, b : UInt<1>} @[ParamFunc.scala 60:18]
    fVal.b <= UInt<1>("h0") @[ParamFunc.scala 61:10]
    fVal.d <= UInt<4>("hd") @[ParamFunc.scala 62:10]
    wire resB : { d : UInt<10>, b : UInt<1>} @[ParamFunc.scala 22:26]
    resB <= fVal @[ParamFunc.scala 22:26]
    when io.selB : @[ParamFunc.scala 23:16]
    {
      resB <= tVal @[ParamFunc.scala 24:11]
    }
    io.resA <= resA @[ParamFunc.scala 69:11]
    io.resB <= resB @[ParamFunc.scala 70:11]

