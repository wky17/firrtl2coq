FIRRTL version 4.0.0
circuit Foo:
  public module Foo:
    input a:
      ;; snippetbegin
      { word : UInt<32>, valid : UInt<1>, flip ready : UInt<1> }
      ;; snippetend
