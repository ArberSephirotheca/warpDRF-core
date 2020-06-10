# Major result

A state in `Conc` is safe if, and only if, a state in `SymHist` is safe
## Proof

`Conc + Hist.Safe <-> LoopFree + Hist.MSafe  <-> SymHist + Hist.StrongSafe`

1. Prove that `Conc` is safe if, and only if `LoopFree` is safe (`LoopFree.v`)
2. Prove that if `LoopFree` is safe, then `SymHist` is safe (`SHComplete.v`)
3. Prove that if `SymHist` is safe, then `LoopFree` is safe (`SHSound.v`)

# Module overview
* `Acc.v`: theory of accesses (abstraction over access expressions)
* `Tasks.v`: declares special variables `TID`, `T1`, and `T2`, which are all different from each other and `TID_COUNT >= 2`
* `Exp.v`: numeric and boolean expressions
* `Conc.v`: multithreaded code with loops
* `ConcImpl.v`: implementation of `Conc`
* `LoopFree.v`: runs `Conc1` but handles loops as variable declaration, ie, running each iteration in its own independent execution thread; proof that `Conc` is safe iff `LoopFree` is safe
* `SymHist.v`: a sequential symbolic history
* `SHCompiler.v`: takes a `LoopFree` program and outputs a `SymHist` program
* `SHSound.v`: proves that if `SymHist` is safe, then `LoopFree` is safe
* `SHComplete.v`: proves that if `LoopFree` is safe, then `SymHist` is safe
* `MultiHist`: theories on multi-histories
# Misc
* `Var.v` and `Tid.v` and `Loc.v`: meta variables
* `StringUtil.v`: utilities on strings
* `SetTh.v`: theorems on sets (inclusion, equivalence, rewriting on those)
* `Util.v`: theorems on lists and son on
* `RangeList.v`: a sequence that starts in `n1` and goes up to `n2` (but does not include `n2`)
