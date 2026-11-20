# Low FIRRTL generator

Run from `src/ocaml`:

```sh
dune exec ./bin/main_lo.exe -- demo/lo/A.lo.fir /tmp/A_lo.v
```

The independent generator emits `generated_lo_circuit : fcircuit VarOrder.T`.
It accepts explicit ground types and rejects aggregates, array accesses,
inferred memory ports and `when`. Memory and instance port references are
mapped to scalar identifiers. It reuses the existing parser and operator
conversion helpers, without modifying the hi generator.

Assertions and assumptions are collected separately as module identifiers,
enable expressions and predicate expressions. Properties now use `LoVerification.all_instances` and `LoCircuit.run_circuit`.
Each assertion produces a lemma admitted as a proof obligation. Lemmas quantify
over input traces and require all assumptions at every nonempty execution
prefix, including the final cycle. The reset-only snapshot is excluded. `current_values` is the settled
pre-edge snapshot; next-state fields are not used to evaluate assertions.
The verification library must be compiled before generated files. Compiling output does not establish that
`LoCircuit.run_circuit` accepts the circuit: external modules and unsupported
memory latencies/read-under-write policies can still be represented in syntax.

The repository's compiled dependencies currently require Coq 8.20:

```sh
opam exec --switch=firrtl2coq-8.20.1 -- coqc \
  -Q lib/simplssrlib simplssrlib -Q lib/nbits nbits -R src firrtl /tmp/A_lo.v
```

Run the Coq command from the repository root.
