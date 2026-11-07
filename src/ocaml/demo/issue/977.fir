circuit top_mod :
  module top_mod :
    input clock: Clock
    input reset_wky: UInt<1>
    input arst: AsyncReset
    input inp_ab: SInt<7>[3]
    output fsm_22_next: UInt<2>
    reg fsm_22_state: UInt<2>, clock with: (reset => (arst, UInt<2>(0)))
    when eq(fsm_22_state, UInt<2>(0)) :
    {
      when xorr(inp_ab[1]) :
      {
        fsm_22_next <= UInt<2>(1)
      }
      else :
      {
        fsm_22_next <= fsm_22_state
    }
    }
    else :
    {
      fsm_22_next <= fsm_22_state
    }
    fsm_22_state <= fsm_22_next