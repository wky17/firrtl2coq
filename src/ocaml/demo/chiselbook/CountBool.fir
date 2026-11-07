circuit CountBool :
  module CountBool :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip in : UInt<1>[9], out : UInt<4>}

    node _io_out_T = add(io.in[0], io.in[1]) @[Bitwise.scala 51:90]
    node _io_out_T_1 = bits(_io_out_T, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_2 = add(io.in[2], io.in[3]) @[Bitwise.scala 51:90]
    node _io_out_T_3 = bits(_io_out_T_2, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_4 = add(_io_out_T_1, _io_out_T_3) @[Bitwise.scala 51:90]
    node _io_out_T_5 = bits(_io_out_T_4, 2, 0) @[Bitwise.scala 51:90]
    node _io_out_T_6 = add(io.in[4], io.in[5]) @[Bitwise.scala 51:90]
    node _io_out_T_7 = bits(_io_out_T_6, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_8 = add(io.in[7], io.in[8]) @[Bitwise.scala 51:90]
    node _io_out_T_9 = bits(_io_out_T_8, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_10 = add(io.in[6], _io_out_T_9) @[Bitwise.scala 51:90]
    node _io_out_T_11 = bits(_io_out_T_10, 1, 0) @[Bitwise.scala 51:90]
    node _io_out_T_12 = add(_io_out_T_7, _io_out_T_11) @[Bitwise.scala 51:90]
    node _io_out_T_13 = bits(_io_out_T_12, 2, 0) @[Bitwise.scala 51:90]
    node _io_out_T_14 = add(_io_out_T_5, _io_out_T_13) @[Bitwise.scala 51:90]
    node _io_out_T_15 = bits(_io_out_T_14, 3, 0) @[Bitwise.scala 51:90]
    io.out <= _io_out_T_15 @[CountBool.scala 10:10]

