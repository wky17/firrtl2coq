FIRRTL version 4.0.0
circuit Bar:
  ;; snippetbegin
  public module Bar :
    output io : { x : UInt<8>, flip y : UInt<8> }
    connect io.x, add(io.y, UInt(1))
  ;; snippetend
