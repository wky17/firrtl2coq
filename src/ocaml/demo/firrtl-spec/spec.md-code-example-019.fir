FIRRTL version 4.0.0
circuit Foo:
  ;; snippetbegin
  public module Foo :
    wire v : UInt<8>[3]
    connect v[0], UInt(0)
    connect v[1], UInt(10)
    connect v[2], UInt(42)
  ;; snippetend
