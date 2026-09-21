# Independent-execution baseline

`Semantics.v` adds independently scheduled reads, writes, and sequencing using
Faial's `Approx.D.Lang`, substitution, memory, and access records. A state holds
shared memory and one remaining program per thread; list indices are thread
identifiers. Memory writes are immediately visible, and a fixed `input` function
supplies initial values. Observations record accesses and their values.

`advance` steps a selected thread. `execution` permits any successful selection;
`run` follows a supplied schedule. `run_sound` and `run_complete` connect them.
`None` means a selection cannot execute, not that the kernel has terminated.
Only `finished` identifies termination; exhausting a schedule does not.

The supported fragment is `Read`, `Write`, `Seq`, and `Skip`. Reads bind values
in their explicit continuations; unbound expressions do not evaluate.
Control flow, declarations, barriers, collectives, dynamic blocks, and weak
memory are not implemented. This increment does not prove the WarpDRF theorem.
Next is matched full-warp synchronization, before adding weak memory.

## Verification

The nine lemmas and fifteen examples check scheduling-dependent outputs,
memory values, traces, invalid selections, and preservation of thread state.
All compile, pass the kernel check, and are closed under the global context:

```sh
dune build
rocq check -silent -Q _build/default/src Faial \
  Faial.Warp.Semantics Faial.Warp.Examples
```

Tested with Rocq 9.1.1, Stdlib 9.0.0, Dune 3.23.1, OCaml 5.2.1, and
[Aniceto](https://gitlab.com/cogumbreiro/aniceto-coq) 1.0.0 at commit
`93d736307ae1799f68c10aa6fb3fb61ee08232e3`.
To reuse the isolated local toolchain from the repository root:

```sh
OPAMROOT=/private/tmp/warpdrf-opam-root-20260921 \
OCAMLPATH=/private/tmp/warpdrf-opam-root-20260921/warpdrf/lib \
LIBRARY_PATH=/opt/homebrew/opt/gmp/lib \
opam exec --switch=warpdrf -- dune build -j 4
```
