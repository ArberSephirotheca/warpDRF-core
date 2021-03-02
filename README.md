
# Languages

* `ULang.v`: unsynchronized protocols ($`\mathcal U`$)
* `WLang.v`: well-formed protocols ($`\mathcal W`$)
* `TLang.v`: symbolic traces ($`\mathcal T`$)
* `ALang.v`: aligned language ($`\mathcal A`$)

# Barrier aligning
* `Align.v`: barrier aligning (function align) + proofs

# Barrier splitting
* `Sequentialize.v`: sequentialization of an unsynchronized protocol into a symbolic trace
* `PhaseSplit.v`: the barrier splitting function + language

# Misc
* `AExp.v`: theory of accesses (abstraction over access expressions)
* `BExp.v`: boolean expressions
* `NExp.v`: numeric expressions
* `RExp.v`: range expressions

# Set of accesses/Lists of set of accesses
* `Hist.v`: notions of DRF on list of accesses, list of list of accesses
* `VHist.v`: nonempty list of list of accesses (used in symbolic traces)
* `MultiHist.v`: list of list of accesses

# Implementation and instantiation of theories
* `ConcImpl.v`: implementation of usync
* `AccExpImpl.v`: one dimensional arrays

# Identifiers
* `Tasks.v`: declares special variables `TID`, `T1`, and `T2`, which are all
  different from each other and `TID_COUNT >= 2`
* `Loc.v`: data type to represent locations
* `Tid.v`: task identifier
* `Var.v`: a variable data type

# Utilities
* `TicTac.v`: tactics
* `InUtil.v`: membership on lists
* `PairInUtil.v`: pair member on lists
* `Util.v`: remaining properties
* `SetTh.v`: set theory results
* `StringUtil.v`: string results
