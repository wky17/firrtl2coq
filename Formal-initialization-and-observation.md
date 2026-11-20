# Formal initialization and assertion observations

The exporter retains the hierarchical FIRRTL AST, bit-vector operations, instance
maps and cycle interpreter. The new wrappers correct initialization and assertion
sampling; they do not substitute a CIRCT model or constrain register enables.

## A real reset edge

For a Chisel top module with an input named `reset` of type `UInt<1>`, `Reset`, or
`AsyncReset`, the frontend records that port's translated identifier and type.
The interpreter receives those values explicitly. It never guesses a numeric ID.
A differently typed port named `reset` is rejected. If no such input is present,
the generator labels and retains the historical structural initialization policy;
it does not silently choose another input as reset.

Low FIRRTL often has `reset => (0, reg)` declarations, with the effective reset in
the next-state mux. Reading the declaration alone therefore does not perform a
reset. `formal_run_after_reset` instead:

1. Builds the original hierarchical initial maps and initializes memories from
   the existing universally quantified `memory_initialization` argument.
2. Initializes every register leaf to a universally quantified bit-vector from
   `formal_symbolic_inputs (inputs 0)`. No unreset register is fixed to zero.
3. Executes one original `circuit_formal_cycle` using `inputs 0` with only the
   named reset port forced high. All data and enable inputs remain unconstrained.
4. Executes `k` ordinary cycles using the original `circuit_formal_run`, consuming
   `inputs 1` through `inputs k`. There is no further initialization/resampling.

Input slot 0 is reserved exclusively for the synthetic reset edge. Ordinary
cycle n consumes input slot n+1, so reset data/enables and invalid choices are
independent of every post-reset cycle. Subsequent reset and register enables
remain arbitrary. Initial register choices use sites `[0; register-id]`. Those sites have
even length, while the existing invalid-statement sites have odd length
`1 + 2 * when-depth`, so the two sources do not alias. Instance paths and
aggregate leaf paths remain distinct as in the original symbolic input API.

`generated_initial_state` now takes `formal_inputs` and returns the state after
this real reset edge. `generated_run` uses the same initialization.
`generated_run_with_choices` adapts the existing per-cycle N-valued choices with
`formal_input_of_choices` and calls the same wrapper; it no longer uses a
conflicting initialization convention for reset-bearing tops.

## Stable observations

`generated_observe k` uses the registers after the reset edge and `k` ordinary
edges, together with `inputs (S k)`. It executes only the original combinational
settling iterations, with register updates disabled. Assertions and assumptions
therefore read one consistent before-edge snapshot. They do not mix next-cycle
registers with previous-cycle cached nodes. The theorem target remains universal
in `k`, including `k = 0` immediately after reset.

## The input domain

`formal_inputs` contains a generic interpreter value map, so it can syntactically
hold `Uninitialized`, `Needtobedefined`, or `Undefinedonpurpose` markers. These are
not concrete hardware port values. `generated_legal_trace` explicitly requires
`formal_external_inputs_defined` for the reset input `inputs 0` and each ordinary observation input `inputs (S j)`,
`0 <= j <= k`.

The predicate checks the declared type and bit width of every actual input leaf,
recursing through arrays, bundles and flip directions. Output-only leaves impose
no constraint. Missing input leaves, wrong widths/types and unknown markers at
input leaves are rejected. Clock and reset ports must be concrete one-bit values;
no clock value, enable pattern, arithmetic result or state invariant is assumed.
For the synthetic reset cycle the only overridden port is the recorded one-bit
reset, set to a concrete value of its declared type. Its other inputs come from
the already checked `inputs 0`.

The trace also requires successful stable observation and the source's explicit
assumptions at every observation `0..k`, including the current assertion sample.
It does not assume the assertions themselves. Generated `Admitted` lemma bodies
remain proof templates, not completed proofs.

## Regressions

- `src/FormalInitializationChecks.v`: Low-FIRRTL reset muxes, arbitrary unreset
  values, no repeated sampling, unrestricted reset-cycle enables, concrete input
  widths and aggregate direction checks.
- `src/ObservationChecks.v`: consistent initial/first/second observation samples,
  and assumption coverage at the initial and historical samples. Its fixture is
  `src/ocaml/test/fixtures/observation.lo.fir`.
- `src/ocaml/test/test_ocaml.ml`: duplicate module-local assert/assume labels and
  reset metadata whose translated port ID is not the usual second port.

Build the Coq project with `_CoqProject`; run OCaml regressions with
`dune runtest --root src/ocaml`. These regressions do not prove the full multiplier
or divider assertions.

## Rebuilding after a semantics patch

Use the source build in this order (inside the configured Coq/opam environment):

```sh
coq_makefile -f _CoqProject -o Makefile
make -j4
dune build --root src/ocaml
dune runtest --root src/ocaml
```

`src/Extract.v` regenerates the ignored `src/ocaml/extraction/*.ml` files from the
checked Coq semantics. Running dune alone can reuse stale extracted code from an
earlier semantics version. A redistributed binary/library bundle must be rebuilt
from the patched tree and include `FormalInitialization` and its dependencies.
The unrelated arithmetic CIRCT export bundle does not need repackaging for these
firrtl2coq changes.

The settling budget now counts every concrete instance, rather than each module
definition only, including combinational nodes, assignments, invalid assignments
and non-root interface synchronization. `NodeIterationChecks` contains a pair of
24-node instances connected in series: the former definition-only budget of 28
left the register pending; the instance budget of 57 reaches its concrete value.
