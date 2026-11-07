circuit FunctionalAdd :
  module FunctionalAdd :
    input clock: Clock
    input reset1 : UInt<1>
    output io : { flip in : UInt<10>[5], res : UInt<10>}

    node _sum_T = add(io.in[3], io.in[4]) @[functional.scala 29:30]
    node _sum_T_1 = tail(_sum_T, 1) @[functional.scala 29:30]
    node _sum_T_2 = add(io.in[0], io.in[1]) @[functional.scala 29:30]
    node _sum_T_3 = tail(_sum_T_2, 1) @[functional.scala 29:30]
    node _sum_T_4 = add(io.in[2], _sum_T_1) @[functional.scala 29:30]
    node _sum_T_5 = tail(_sum_T_4, 1) @[functional.scala 29:30]
    node _sum_T_6 = add(_sum_T_3, _sum_T_5) @[functional.scala 29:30]
    node sum = tail(_sum_T_6, 1) @[functional.scala 29:30]
    io.res <= sum @[functional.scala 32:10]

