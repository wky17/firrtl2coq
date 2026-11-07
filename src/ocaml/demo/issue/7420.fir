FIRRTL version 4.0.0
circuit Block: 
  module A:
    input x : UInt<1>
    output y : UInt<1>

    connect y, UInt<1>(0)

    when x :
    {
      node n = x
      connect y, UInt<1>(1)
    }
    else :
    {
      skip
 }

  module B:
    input x : UInt<1>
    output y : UInt<1>

    connect y, UInt<1>(0)

    when x :
    {
      node n = x
    }
    else :
    {
      connect y, UInt<1>(1)
      skip
 }

  public module Block:
    input x : UInt<1>
    output y : UInt<1>

    inst a aof A
    connect a.x, x
    inst b aof B
    connect b.x, x

    connect y, and(a.y, b.y)
    