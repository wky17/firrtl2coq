FIRRTL version 4.0.0
circuit MyModule:
  ;; snippetbegin
  public module MyModule :
    input portx: {b: UInt<1>, c: UInt<2>}
    input porty: UInt<1>
    output myport: {b: UInt<1>, c: UInt<2>}
    connect myport, portx
  ;; snippetend
