circuit top_mod :
  module mod_2 :
    input clock: Clock
    input reset_wky: UInt<1>
    input inp_a: {inp_d: UInt<14>}
  module top_mod :
    input clock: Clock
    input reset_wky: UInt<1>
    inst U0 aof mod_2
    U0 is invalid
    U0.reset_wky <= reset_wky
    U0.clock <= clock