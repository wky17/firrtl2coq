FIRRTL version 4.0.0
circuit MyModule:
  ;; snippetbegin
  public module MyModule :
    input a: UInt<3>
    input b: UInt<3>
    input en: UInt<1>
    wire x: UInt<3>
    when en :
    {
      connect x, a
    }
    else :
    {
      connect x, b
    }
  ;; snippetend
