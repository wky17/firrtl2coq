circuit FunctionalComp :
  module FunctionalComp :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip a : UInt<8>, flip b : UInt<8>, equ : UInt<8>, gt1 : UInt<8>}

    node equResult = eq(io.a, io.b) @[functional.scala 52:17]
    node gtResult = gt(io.a, io.b) @[functional.scala 53:16]
    node equ = eq(io.a, io.b) @[functional.scala 52:17]
    node gt1 = gt(io.a, io.b) @[functional.scala 53:16]
    io.equ <= equResult @[functional.scala 68:10]
    io.gt1 <= gtResult @[functional.scala 69:9]
    io.equ <= equ @[functional.scala 71:10]
    io.gt1 <= gt1 @[functional.scala 72:9]

