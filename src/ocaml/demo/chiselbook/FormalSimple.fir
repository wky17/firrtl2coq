circuit FormalSimple :
  module FormalSimple :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip a : UInt<10>, flip b : UInt<10>, y : UInt<10>}

    node _io_y_T = and(io.a, io.b) @[formal.scala 10:16]
    io.y <= _io_y_T @[formal.scala 10:8]

