circuit Bar :
  module Bar:
    input a: {a: UInt<1>}
    input clk: Clock
    output b: {a: UInt<1>}

    reg x: {a: UInt<1>}, clk

    x.a <= a.a
    b.a <= x.a