FIRRTL version 4.0.0
circuit MyModule:
  ;; snippetbegin
  public module MyModule :
    input a: UInt<3>
    input b: UInt<3>
    input c: UInt<3>
    input d: UInt<3>
    input c1: UInt<1>
    input c2: UInt<1>
    input c3: UInt<1>
    wire x: UInt<3>
    when c1 :
    {
      connect x, a
    }
    else :
    {  when c2 :
        {
          connect x, b
        }
      else :
        {
        when c3 :
          {
            connect x, c
          }
        else :
          {
            connect x, d
          }
        }
    }
  ;; snippetend
