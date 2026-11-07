circuit UseAdder :
  module ParamAdder :
    input clock: Clock
    input reset_wky: Reset
    output io : { flip a : UInt<8>, flip b : UInt<8>, c : UInt<8>}

    node _io_c_T = add(io.a, io.b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io.c <= _io_c_T_1 @[ParamAdder.scala 11:8]

  module ParamAdder_1 :
    input clock: Clock
    input reset_wky: Reset
    output io : { flip a : UInt<16>, flip b : UInt<16>, c : UInt<16>}

    node _io_c_T = add(io.a, io.b) @[ParamAdder.scala 11:16]
    node _io_c_T_1 = tail(_io_c_T, 1) @[ParamAdder.scala 11:16]
    io.c <= _io_c_T_1 @[ParamAdder.scala 11:8]

  module UseAdder :
    input clock: Clock
    input reset_wky: UInt<1>
    output io : { flip x : UInt<16>, flip y : UInt<16>, res : UInt<16>}

    inst add8 aof ParamAdder @[ParamAdder.scala 23:20]
    add8.clock <= clock
    add8.reset_wky <= reset_wky
    inst add16 aof ParamAdder_1 @[ParamAdder.scala 24:21]
    add16.clock <= clock
    add16.reset_wky <= reset_wky
    add16.io.a <= io.x @[ParamAdder.scala 27:14]
    add16.io.b <= io.y @[ParamAdder.scala 28:14]
    node _io_res_T = or(add16.io.c, add8.io.c) @[ParamAdder.scala 29:24]
    io.res <= _io_res_T @[ParamAdder.scala 29:10]
    add8.io.a <= io.x @[ParamAdder.scala 31:13]
    add8.io.b <= io.y @[ParamAdder.scala 32:13]

