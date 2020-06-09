# Major result

A state in `Conc1` is safe if, and only if, a state in `Conc2` is safe
## Proof
1. Prove that `Conc1` is safe if, and only if `LoopFree` is safe (`LoopFree.v`)
2. Prove that if `LoopFree` is safe, then `Conc2` is safe (`Conc2Complete.v`)
3. Prove that if `Conc2` is safe, then `LoopFree` is safe (`Conc2Sound.v`)

# Module overview
* `Acc.v`: theory of accesses (abstraction over access expressions)
* `Tasks.v`: declares special variables `TID`, `T1`, and `T2`, which are all different from each other and `TID_COUNT >= 2`
* `Exp.v`: numeric and boolean expressions
* `Conc1.v`: multithreaded code with loops
* `Conc1Impl.v`: implementation of `Conc1`
* `LoopFree.v`: runs `Conc1` but handles loops as variable declaration, ie, running each iteration in its own independent execution thread; proof that `Conc1` is safe iff `LoopFree` is safe
* `Conc2.v`: a sequential symbolic history
* `Conc2Compiler.v`: takes a `LoopFree` program and outputs a `Conc2` program
* `Conc2Sound.v`: proves that if `Conc2` is safe, then `LoopFree` is safe
* `Conc2Complete.v`: proves that if `LoopFree` is safe, then `Conc2` is safe
# Misc
* `Var.v` and `Tid.v` and `Loc.v`: meta variables
* `StringUtil.v`: utilities on strings
* `SetTh.v`: theorems on sets (inclusion, equivalence, rewriting on those)
* `Util.v`: theorems on lists and son on
* `RangeList.v`: a sequence that starts in `n1` and goes up to `n2` (but does not include `n2`)
