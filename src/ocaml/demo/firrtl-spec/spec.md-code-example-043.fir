FIRRTL version 4.0.0
circuit MyModule :
  ;; snippetbegin
  public module MyModule :
    input a: UInt<5>
    input b: UInt<5>
    output myport1: UInt<5>
    output myport2: UInt<5>

    connect myport1, a
    connect myport1, b
    connect myport2, a
  ;; snippetend
