From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt ExtrOcamlZInt.
From Coq Require Import Arith List.
From mathcomp Require Import tuple.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env Firrtl Semantics ExpandConnects_inst ExpandWhens_inst Semantics_with_implicit_widths.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/ocaml/extraction".
Separate Extraction
         seq.catrev nat_of_int n_of_int int_of_nat int_of_n int_of_z
         NBitsDef.from_string NBitsDef.from_hex NBitsDef.from_bin
         NBitsDef.to_hex NBitsDef.to_nat NBitsDef.to_bin
         (*LoFirrtl.run_module0 LoFirrtl.run_module
         LoFirrtl.no_mem_run_module_inline LoFirrtl.no_mem_run_module0_inline
         LoFirrtl.no_mem_run_module LoFirrtl.no_mem_run_module0 *)
         (*Semantics.expandconnects Semantics.expandWhens.*)
         ExpandConnects_inst.expandconnects ExpandWhens_inst.expandWhens ExpandConnects_inst.preprocess_subaccess
         Semantics_with_implicit_widths.circuit_value.
Cd "../../..".
