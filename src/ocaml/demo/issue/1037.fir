circuit Test :
    module Test :
        input p : UInt<1>
        wire x : UInt<32>
        when p :
        {
            x <= UInt(1)
        }
        x <= UInt(1)