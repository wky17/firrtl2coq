FIRRTL version 4.0.0
;; snippetbegin
circuit Foo :
    public module Foo :
     input a: UInt<1>
     output b: UInt<1>
     when a:
     {
         connect b, a
     }
     else:
     {
       connect b, not(a)
}
;; snippetend
