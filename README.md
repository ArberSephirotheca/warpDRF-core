
# Languages

* `Conc.v`: unsynchronized protocols
* `WLang.v`: well-formed protocols
* `SymHist.v` + `SymExec.v`: symbolic traces
* `AlignLang.v`: aligned language

# Barrier aligning
* `Align.v`: barrier aligning (function align) + proofs

# Barrier splitting
* `SHCompiler.v`: barrier splitting (just projection)
* `SHResults.v`: barrier splitting (completeness and correctness)
* `PhaseSplit.v`: the barrier splitting function + language

# Misc
* `AccExp.v`: theory of accesses (abstraction over access expressions)
* `AccExpImpl.v`: one dimensional arrays
* `Tasks.v`: declares special variables `TID`, `T1`, and `T2`, which are all
  different from each other and `TID_COUNT >= 2`
* `NExp.v`: numeric expressions
* `BExp.v`: boolean expressions
* `RExp.v`: range expressions
* `Hist.v`: notions of DRF on history/multi history
* `MultiHist.v`: memory equivalence lemmas
* `Var.v`: a variable data type
* `VHist.v`: notion of histories used in symbolic traces
* `ConcImpl.v`: implementation of usync
* `Loc.v`: data type to represent locations (unused)
* `InUtil.v`: membership on lists
* `PairInUtil.v`: pair member on lists
* `Util.v`: remaining properties
* `SetTh.v`: set theory results
* `StringUtil.v`: string results
* `TicTac.v`: tactics
* `Tid.v`: task identifier
