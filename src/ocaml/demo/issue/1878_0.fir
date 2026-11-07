circuit CountAndDriver :
  module CountAndDriver :
    input clock : Clock
    input reset_wky : UInt<1>
    output io : { flip default_value : UInt<1>, flip count : UInt<16>, driven_value : UInt<1>}

    clock is invalid
    reset_wky is invalid
    io is invalid
    io.driven_value <= UInt<1>("h1") 
    reg counter : UInt<16>, clock with :
      reset => (reset_wky, UInt<16>("h0")) 
    node _T = not(io.default_value) 
    when _T : 
    {
      node _T_1 = lt(counter, io.count)
      when _T_1 : 
      {
        node _counter_T = add(counter, UInt<1>("h1")) 
        node _counter_T_1 = tail(_counter_T, 1) 
        counter <= _counter_T_1 
    }
    }
    node _T_2 = leq(io.count, counter) 
    when _T_2 :
    {
      io.driven_value <= io.default_value    }
