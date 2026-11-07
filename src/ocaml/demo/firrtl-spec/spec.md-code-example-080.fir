FIRRTL version 4.0.0
circuit Foo:
  public module Foo:
    wire mymem:
      ;; snippetbegin
      {flip r1: {addr: UInt<8>,
                 en: UInt<1>,
                 clk: Clock,
                 flip data: {real: SInt<16>, imag: SInt<16>}},
       flip r2: {addr: UInt<8>,
                 en: UInt<1>,
                 clk: Clock,
                 flip data: {real: SInt<16>, imag: SInt<16>}},
       flip w:  {addr: UInt<8>,
                 en: UInt<1>,
                 clk: Clock,
                 data: {real: SInt<16>, imag: SInt<16>},
                 mask: {real: UInt<1>, imag: UInt<1>}}}
      ;; snippetend
