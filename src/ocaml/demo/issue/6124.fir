circuit Test:
  module Queue_2:
    input clock: Clock
    input reset_wky: UInt<1>
    input io_enq_valid: UInt<1>
    output io_enq_ready: UInt<1>
    input io_enq_bits: { a0: UInt<8>, a1: UInt<8>, a2: UInt<8>, a3: UInt<8>, a4: UInt<8> }
    output io_deq_valid: UInt<1>
    input io_deq_ready: UInt<1>
    output io_deq_bits: { a0: UInt<8>, a1: UInt<8>, a2: UInt<8>, a3: UInt<8>, a4: UInt<8> }

  module Test:
    input clock: Clock
    input reset_wky: UInt<1>
    input io_in: { a0: UInt<8>, a1: UInt<8>, a2: UInt<8>, a3: UInt<8>, a4: UInt<8> }
    output io_out: { a0: UInt<8>, a1: UInt<8>, a2: UInt<8>, a3: UInt<8>, a4: UInt<8> }

    inst q aof Queue_2
    q.clock <= clock
    q.reset_wky <= reset_wky
    q.io_enq_valid <= UInt<1>(1)
    q.io_enq_bits <= io_in
    q.io_deq_ready <= UInt<1>(1)
    io_out <= q.io_deq_bits
