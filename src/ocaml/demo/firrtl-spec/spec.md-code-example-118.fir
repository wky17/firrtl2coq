FIRRTL version 4.0.0
circuit IValue:
  ;; snippetbegin
  public module IValue :
    output o : UInt<8>
    input c : UInt<1>
    input v : UInt<8>

    wire a : UInt<8>
    invalidate a
    when c :
    {
      connect a, v
    }
    connect o, a
  ;; snippetend
