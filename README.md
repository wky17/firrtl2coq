# firrtl2coq

A Coq formalization of FIRRTL together with an OCaml-based translator that
generates Coq code from FIRRTL circuits. The generated Coq files can be
compiled against the libraries in this repository and used for formal
reasoning about digital circuits.

---

## Overview

This repository contains:

- A Coq formalization of FIRRTL semantics (`src/`).
- An OCaml extractor/translator that converts FIRRTL circuits into Coq
  (`src/ocaml/`).
- Supporting Coq libraries for bit-vectors and ssreflect simplification
  (`lib/nbits`, `lib/simplssrlib`).
- Example FIRRTL circuits and a minimal Coq test (`demo/`, `TestAdder.v`).

The typical workflow is:

1. Build the Coq development.
2. Build the OCaml translator with dune.
3. Translate a FIRRTL file into a Coq file.
4. Compile the generated Coq file against this repository's libraries.

---

## Requirements

The following versions are known to work:

| Dependency | Version |
|------------|---------|
| [Coq](https://coq.inria.fr) | 8.16.0 |
| [MathComp](https://github.com/math-comp/math-comp) | 1.15.0 |
| [OCaml](https://ocaml.org) | 4.14.2 |
| [dune](https://dune.build) | any recent version |

We recommend installing Coq, MathComp and OCaml through
[opam](https://opam.ocaml.org):

```bash
opam switch create firrtl2coq 4.14.2
eval $(opam env)
opam install coq.8.16.0 coq-mathcomp-ssreflect.1.15.0 dune
```

If you already have a compatible opam switch, simply install the missing
packages:

```bash
opam install coq.8.16.0 coq-mathcomp-ssreflect.1.15.0 dune
```

---

## Getting the Source

```bash
git clone https://github.com/wky17/firrtl2coq.git
cd firrtl2coq
```

---

## Building the Coq Development

Generate the `Makefile` from `_CoqProject` and build all Coq files:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

After a successful build, the minimal example `TestAdder.v` should compile.
It contains a small FIRRTL circuit expressed in Coq syntax:

```bash
coqc -Q lib/simplssrlib simplssrlib \
     -Q lib/nbits nbits \
     -R src firrtl \
     TestAdder.v
```

If `TestAdder.vo` is produced without errors, the Coq side of the project is
ready.

---

## Building the OCaml Translator

The translator lives under `src/ocaml` and is built with dune:

```bash
cd src/ocaml
dune build
```

This produces the executable `./bin/main.exe` (relative to `src/ocaml`).

---

## Usage: Translating a FIRRTL Circuit

The translator takes a FIRRTL file and writes a Coq file. For example, to
translate `demo/CoreSoc.hi.fir` into `CoreSoc_memory.v`:

```bash
cd src/ocaml
dune exec ./bin/main.exe -- \
  demo/CoreSoc.hi.fir \
  CoreSoc_memory.v
```

Then compile the generated Coq file from the repository root, so that the
`firrtl`, `simplssrlib` and `nbits` libraries are visible to Coq:

```bash
cd ../..
coqc -Q lib/simplssrlib simplssrlib \
     -Q lib/nbits nbits \
     -R src firrtl \
     CoreSoc_memory.v
```

If compilation succeeds, `CoreSoc_memory.vo` is produced and the
translated circuit is available for further Coq proofs.

## Repository Layout

```
.
├── _CoqProject              # Coq project description
├── lib/
│   ├── nbits/               # Bit-vector library
│   └── simplssrlib/         # ssreflect simplification library
├── src/                     # Coq formalization of FIRRTL
│   ├── TestAdder.v              # Minimal Coq example of a FIRRTL circuit
│   └── Semantics_with_memory.v        # HiFirrtl semantics in Rocq
└── src/ocaml/               # OCaml translator (dune project)
    ├── bin/main.exe         # Translator executable
    └── demo/                # Example FIRRTL circuits (e.g. CoreSoc.hi.fir)
```
