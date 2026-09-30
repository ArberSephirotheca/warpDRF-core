# Warp agreement proofs

These files mechanize the WarpDRF contract for one warp with nested
conditionals, several collectives, and structured loops with `Break` and
`Continue`. Memory is sequentially consistent.

## Main results

- `Agree.v` proves `sso_agreement`, Theorem 1 of the paper for SSO. Under
  reference memory DRF, every completed SSO execution forms the reference's
  group at every collective instance, gives each thread the same reads, and
  leaves the same final memory. The proof uses only condition 1
  (`agreement_from_drf`); the groups are part of the conclusion.
- `sso_every_run_agreement` extends this to every SSO run, finished or not.
  Every collective it has run so far formed the reference's group, every read
  so far returned the reference's value, and the run can still complete with
  the reference's observations.
- `Spec.v` shows that Spec, which fires a collective with whichever threads
  have arrived, is not a conforming target. On a kernel that is WarpDRF for
  `StructuredPartial`, the group of a collective under Spec depends on the
  schedule (`spec_grouping_depends_on_schedule`), so the guarantee of
  `sso_agreement` fails for Spec (`warpdrf_fails_under_spec`). Counting
  unfinished runs, the guarantee also fails under `FullWarp`
  (`warpdrf_fails_under_spec_every_run`).

## The model

- `Store.v`: shared memory. Writes are immediately visible, and a fixed `input`
  function supplies the initial value of every location. An observation
  records one access and the value it read or wrote.
- `Code.v`: kernel code. It has reads that bind a variable, writes, sequencing,
  conditionals, loops, `Barrier n`, and `AddZero`, which is `subgroupAdd(0)`
  with its unused zero result. `Loop body` repeats `body` until a `Break`;
  `Continue` ends the current iteration early. A running loop is
  `Iter k rest body`: iteration `k`, with `rest` left in it. `step` is one step
  of one thread; a collective does not step on its own.
- `Model.v`: SSO. Each collective is named by its site: `AddZero` has one site
  and `Barrier n` has site `n`. Its dynamic block, its instance, is the site
  together with the iteration counts of the loops around it, outermost first.
  A collective after a loop drops that loop's count, so threads that leave the
  loop in different iterations meet there.
  - `reach c s v` says whether a thread with remaining code `c` may still run
    site `s` at counts `v`. Before a conditional, a thread may reach the sites
    of both branches; once it takes one, the other is dropped. In iteration
    `k`, a thread may reach `k :: v'` through the rest of the iteration and any
    `j > k` through the loop body.
  - A release of an instance is enabled when some thread waits there and no
    other thread may still reach it; the waiting threads form the group. This
    is SIMT-Step's rule that a collective waits until its unknown set is empty,
    with the unknown set computed from the code.
  - `step_reach` and `release_reach` show that steps and releases never enlarge
    `reach`: a thread that has left an instance behind cannot come back to it.
- `Order.v`: the happens-before of condition 1. It is the transitive closure of
  each thread's program order, in which a collective belongs to every
  participant. With several collectives, a write can reach a read only through
  a relay thread (`relay` in `Tests.v`). Only events with no common thread
  swap; the permitted swaps preserve memory DRF and each thread's read history.
- `Commute.v`: the facts the agreement proof uses. A thread step and a release
  commute, releases of different instances commute, enabled actions stay
  enabled, and finished states enable nothing.
- `Agree.v`: the reference run, the contract, and agreement (below).
- `Blocks.v`: in a well-sited kernel each instance forms at most one group
  (`instance_released_once`), so no thread arrives after a release.
- `Spec.v`: the Spec target (below).
- `Tests.v`: examples (below).

## Reference run and contract

`run fuel input programs` is the reference execution. It runs the lowest
runnable thread and releases an instance only when no thread can run. Loops can
run forever, so the run takes a step budget. It accepts only well-sited source
programs, in which no thread's code names a site twice, so an instance is one
dynamic block. `run_sound` proves that a successful run is a completed SSO
execution. The run also executes racy programs; checking memory DRF is
separate.

`conditions` conjoins `MemDRF` with `UnambiguousParticipation`. Both are
checked on the kernel and its reference trace, never on target executions.
Condition 2 requires every recorded group to be nonempty and to contain
distinct threads of the warp, and it applies the configuration's placement
rule:

- `FullWarp`: every group is the whole warp, and every thread runs one program
  whose collectives sit where every thread takes the same path
  (`warp_uniform`). A test that decides whether a collective runs, or whether a
  loop with a collective ends its iteration, must be closed: it mentions
  neither the thread identifier nor a value read from memory. Branches without
  a collective may still diverge. The rule is conservative for loops: a loop
  that contains a collective exits in its first iteration or never, and a loop
  bound read from memory is not recognized as uniform.
- `StructuredPartial`: admits the partial groups the reference forms.
  `reference_structured_partial` proves that every reference run passes this
  check, so under this configuration the participation premise holds
  automatically.

`same_observations` compares the group of every instance, each thread's
ordered read history (addresses and values), and the final value at every
location. It does not require the same global event order or the same internal
representation of the memory map.

## Agreement proof

`completed_agreement` matches any completed execution with a completed
memory-DRF one from the same state. The target schedule supplies the next
action, and `pull_enabled` moves that action to the front of the reference
execution. Each reordering preserves memory DRF, so no target schedule is
assumed to be DRF. `agreement_from_drf` applies this to the reference run, and
`sso_agreement` follows. `target_memory_drf` proves that completed target
traces are memory-DRF.

The target run never has to finish: `pull_enabled` needs only the reference to
be complete. `prefix_agreement` aligns an unfinished run the same way, and the
rest of the rearranged reference then completes it. `sso_every_run_agreement`
states the result as the guarantee for every run, using `observations_so_far`:
each instance's groups and each thread's reads so far are the first ones of
the reference.

## Spec

Spec is SIMT-Step's speculative target. It fires a collective as soon as some
thread waits there, with whichever threads have arrived, like `__activemask()`;
it does not wait for the unknown set to empty. SIMT-Step prunes a run in which
a thread arrives after the firing. Here each instance fires at most once, so
such a thread waits forever and the run never completes. This rule belongs to
Spec, not to WarpDRF. Thread steps are the SSO thread steps.

`spec_grouping_depends_on_schedule` shows that Spec does not conform to
`StructuredPartial`. In `single_writer`, both threads read a flag and, when it
is zero, meet at `AddZero`; afterwards thread 0 sets the flag. The kernel meets
both `StructuredPartial` conditions: the reference orders thread 1's read
before thread 0's write through the collective (`single_writer_memory_drf`),
and every reference run passes the participation check. Under Spec, which
threads join the collective depends on the schedule:

- If thread 1 arrives in time, the collective fires with `[0; 1]`, and the run
  is the reference run (`single_writer_on_time`).
- If thread 0 fires it alone, it then writes 1; thread 1 reads 1 and skips the
  collective (`single_writer_early`). The group and thread 1's read differ from
  the reference.

The theorem states both groups: `[0; 1]` in the reference and the first Spec
run, and `[0]` in the second. So the collective has no fixed group under Spec.
`warpdrf_fails_under_spec` states the consequence. It takes the statement of
`sso_agreement` for `StructuredPartial`, with Spec executions in place of SSO
executions, and proves it false.

Under `FullWarp` every completed Spec run does agree: a collective in uniform
code is reached by every thread, so a thread that Spec leaves out arrives after
the firing, and the run never completes. The failure shows up in unfinished
runs. In `late`, each thread writes its own cell and then calls `AddZero`; the
kernel is WarpDRF for either configuration, and the reference forms `[0; 1]`.
Spec can fire the collective with thread 0 alone (`late_early`), a group the
reference never forms. `warpdrf_fails_under_spec_every_run` takes the statement
of `sso_every_run_agreement` for either configuration, with Spec executions in
place of SSO executions, and proves it false.

## Examples

`Tests.v` computes reference traces and proves the group of an instance in
every completed execution for these kernels:

- nested sites and two independent halves of the warp;
- `partial`, where only thread 0 runs `AddZero`;
- a `Break` from a conditional and a `Continue`, each of which excludes a thread
  from a barrier in its loop;
- threads that leave a loop in different iterations and meet after it;
- a barrier met by fewer threads in each iteration;
- nested loops.

It also proves thread 2's read in every completed execution of the relay. It
shows that crossed collectives never finish, that the placement rule rejects a
data-dependent `Break` in a loop with a collective, and that a repeated site is
rejected.

## Scope

| Area | Status |
| --- | --- |
| Memory | Sequentially consistent; full agreement for completed runs, agreement so far for unfinished ones |
| Progress | No SSO run of a WarpDRF kernel gets stuck: it can always still complete (`sso_every_run_agreement`). Termination of every schedule is not proved |
| Delayed visibility | Not modeled |
| Warps | One warp; no subgroups inside it and no workgroup barrier |
| Control flow | Nested conditionals and structured loops with `Break` and `Continue`; no `switch` |
| Local state | Loop counters live in memory cells a thread owns; no local variable updates |
| Collectives | `AddZero` and `Barrier n`, which order memory among their participants; no collective results |
| `FullWarp` placement | Conservative for loops, as described above |

## Verification

- `Store.v`, `Code.v`: commuting memory effects, the loop step, its replay
  from an observation, and the swap of steps by different threads.
- `Model.v`: `reach` and its monotonicity under steps and releases.
- `Order.v`: the transitive happens-before and its preservation under swaps.
- `Commute.v`: commutation and persistence of actions.
- `Agree.v`: agreement for every completed SSO execution from reference memory
  DRF alone, agreement so far and completion for every unfinished one,
  memory-DRF preservation, reference-run soundness, and acceptance of every
  reference run by the `StructuredPartial` check.
- `Blocks.v`: at most one group per instance in any execution of a well-sited
  kernel.
- `Spec.v`: a kernel that is WarpDRF for `StructuredPartial`, with two
  completed Spec runs that form different groups, one agreeing with the
  reference and one not, and the failure of the guarantee under Spec; a
  kernel that is WarpDRF for either configuration, with an unfinished Spec run
  that forms a group the reference never forms.
- `Tests.v`: the examples above.

```sh
dune build
rocq check -silent -Q _build/default/src Faial \
  Faial.Warp.Store Faial.Warp.Code Faial.Warp.Model Faial.Warp.Order \
  Faial.Warp.Commute Faial.Warp.Agree Faial.Warp.Blocks Faial.Warp.Spec \
  Faial.Warp.Tests
```

Tested with Rocq 9.1.1, Stdlib 9.0.0, Dune 3.23.1, OCaml 5.2.1, and
[Aniceto](https://gitlab.com/cogumbreiro/aniceto-coq) 1.0.0 at commit
`93d736307ae1799f68c10aa6fb3fb61ee08232e3`.
To reuse the isolated local toolchain from the repository root:

```sh
OPAMROOT=/private/tmp/warpdrf-proof-check-20260928 \
OCAMLPATH=/private/tmp/warpdrf-proof-check-20260928/warpdrf/lib \
LIBRARY_PATH=/opt/homebrew/opt/gmp/lib \
opam exec --switch=warpdrf -- dune build -j 4
```
