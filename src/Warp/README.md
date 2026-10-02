# Warp agreement proofs

These files mechanize the WarpDRF contract for one warp with nested
conditionals, several collectives, and structured loops with `Break` and
`Continue`. Memory is sequentially consistent; `Delayed.v` also covers
delayed visibility.

## Main results

`Guarantee c target` in `Agree.v` states WarpDRF's guarantee for
configuration `c` on a target whose runs, finished or not, are described by
`target`. On a kernel that meets both conditions, no run has a race, and every
finished run forms the reference's group at every collective instance, gives
each thread the same reads, and leaves the same final memory. With delayed
visibility a race aborts the run, as in GPUVerify, so a run fails the guarantee
as soon as it races.

- `sso_agreement : forall c, Guarantee c sso_target` is Theorem 1 of the paper
  for SSO.
- `delayed_agreement : forall c, Guarantee c delayed_target` is the same
  guarantee for SSO with delayed visibility, under the same conditions.
- `warpdrf_fails_under_spec : forall c, ~ Guarantee c spec_target` shows that
  Spec, which fires a collective without waiting for threads that may still
  branch away from it, is not a conforming target, even with the same delayed
  visibility. On a kernel that is WarpDRF for either configuration, the group
  of a collective under Spec depends on the schedule
  (`spec_grouping_depends_on_schedule`).

## The model

- `Store.v`: shared memory. Writes are immediately visible, and a fixed `input`
  function supplies the initial value of every location. An observation
  records one access and the value it read or wrote.
- `Code.v`: kernel code, following the paper's language. It has reads that
  bind a variable, writes, local statements, sequencing, conditionals, loops,
  `Return`, and warp primitives. `Loop body` repeats `body` until a `Break`;
  `Continue` ends the current iteration early; `Return` ends the thread. A
  running loop is `Iter k rest body`: iteration `k`, with `rest` left in it.
  `step` is one step of one thread.
  - `Local x f args body` binds `x` to `f` applied to the values of `args`, a
    thread-local function, and runs `body`. It covers both plain assignment and
    the paper's uninterpreted functions `f(e, ...)`.
  - `Switch e cases default` runs the first case whose label equals `e`. It is
    a chain of conditionals, which gives the reference the same executions.
  - `Prim n sync full f args x body` is a warp primitive with site label `n`.
    Each participant supplies the values of `args` and receives `f` applied to
    the participants' (thread, values) pairs and its own thread; the result is
    bound to `x` in `body`. As in the paper, `f` is uninterpreted: every
    theorem holds for every `f`. `sync` is the paper's `ord(p)`, whether the
    primitive orders memory among its participants, and `full` is `req(p)`,
    whether it requires the whole warp.
  - A thread that reaches a primitive evaluates `args` and waits as `Wait`; the
    warp releases it (`Model.v`).
  - `Barrier n` and `AddZero n` are primitives that order memory, do not
    require the whole warp, and return nothing useful; `AddZero n` stands for
    `subgroupAdd(0)`.
- `Model.v`: SSO. Each primitive is named by its site, its label together with
  its `sync` and `full` flags. A thread is finished when its code is `Skip` or
  `Return`. Its dynamic block, its instance, is the site together with
  the iteration counts of the loops around it, outermost first. A primitive
  after a loop drops that loop's count, so threads that leave the loop in
  different iterations meet there.
  - `reach c s v` says whether a thread with remaining code `c` may still run
    site `s` at counts `v`. Before a conditional, a thread may reach the sites
    of both branches; once it takes one, the other is dropped. In iteration
    `k`, a thread may reach `k :: v'` through the rest of the iteration and any
    `j > k` through the loop body.
  - A release of an instance is enabled when some thread waits there and no
    other thread may still reach it; the waiting threads form the group. This
    is SIMT-Step's rule that a collective waits until its unknown set is empty,
    with the unknown set computed from the code.
  - The release collects the values the group supplied, gives each participant
    its result, and resumes it in the primitive's body (`resume`).
  - `step_reach` and `resume_reach` show that steps and releases never enlarge
    `reach`: a thread that has left an instance behind cannot come back to it.
- `Order.v`: the happens-before of condition 1. It is the transitive closure of
  each thread's program order, in which a primitive that orders memory belongs
  to every participant; one that does not adds no ordering between threads.
  With several collectives, a write can reach a read only through
  a relay thread (`relay` in `Tests.v`). Only events with no common thread
  swap; the permitted swaps preserve memory DRF and each thread's read history.
- `Commute.v`: the facts the agreement proof uses. A thread step and a release
  commute, releases of different instances commute, enabled actions stay
  enabled, and finished states enable nothing.
- `Agree.v`: the reference run, the contract, and agreement (below).
- `Blocks.v`: in a well-sited kernel each instance forms at most one group
  (`instance_released_once`), so no thread arrives after a release.
- `Delayed.v`: SSO with delayed visibility (below).
- `Spec.v`: the Spec target, with delayed visibility (below).
- `Tests.v`: examples (below).

## Reference run and contract

`run fuel input programs` is the reference execution. Like the paper's, it
picks threads in a fixed order: the lowest-numbered thread that can step, and a
collective only when no thread can step. So each kernel and input has
exactly one reference execution. `fuel` bounds the number of steps, since a
loop may not terminate; the theorems cover kernels whose reference run finishes
within it. The run rejects a kernel in which one thread's code contains the
same collective twice (for example two `Barrier 0`s), because a collective is
identified by its name and loop counts. `run_sound` proves that a successful
run is a completed SSO execution. The run also executes racy kernels; memory
DRF is checked separately.

`conditions` conjoins `MemDRF` with `UnambiguousParticipation`. As in the
paper, both are checked on the reference trace, never on target executions.
Condition 2 requires every group the reference forms to be nonempty and to
contain distinct threads of the warp, and adds the configuration's
requirement:

- `FullWarp`: every group is the whole warp. As in the paper, every executed
  collective must include the complete warp; nothing restricts where a
  collective may occur in the code.
- `StructuredPartial`: admits the partial groups the reference forms, except
  that a primitive that requires the whole warp must get it.
  `reference_structured_partial` proves that a reference run passes this check
  as soon as those primitives got the whole warp.

`same_observations` compares the group of every instance, each thread's
ordered read history (addresses and values), and the final value at every
location. It does not require the same global event order or the same internal
representation of the memory map.

## Agreement proof

`prefix_agreement` matches any execution, finished or not, with the start of a
completed memory-DRF one from the same state. The target schedule supplies the
next action, and `pull_enabled` moves that action to the front of the reference
execution. Each reordering preserves memory DRF, so no target schedule is
assumed to be DRF. `pull_enabled` needs only the reference to be complete, so
the target run never has to finish; the rest of the rearranged reference then
completes it.

A finished run has nothing left to complete, so `completed_agreement` is a
corollary: the target trace is a rearrangement of the reference trace, and the
final states hold the same values. `agreement_from_drf` applies it to the
reference run. `target_memory_drf` proves that every target trace, finished or
not, is memory-DRF: it is the start of a rearranged reference
(`memory_drf_app_l`). `sso_agreement` follows.

## Delayed visibility

`Delayed.v` gives SSO the memory of GPUVerify's synchronous, delayed
visibility semantics. A write stays pending: its own thread reads it, other
threads do not. The release of a primitive that orders memory publishes the
pending writes of its participants; a primitive that does not order memory
publishes nothing. As in GPUVerify, a race aborts the run, and `Guarantee`
counts a run whose trace has a race as a failure. The memory a run leaves is
observed with its remaining pending writes published.

GPUVerify's semantics differs in three ways. Its threads run in lock-step,
while ours follow SSO. Its barrier always includes the whole group, while a
warp primitive here may have a partial group; its release publishes its
participants' writes to every thread. It has no single final memory, while we
publish the remaining writes to observe one.

`delayed_agreement` holds under the same conditions, and its proof reuses
`prefix_agreement` unchanged. No run races, by `target_memory_drf` for the SSO
run with the same trace. Each delayed step is the SSO step with the same
action and event (`dstep_matches`). The key fact is `unpublished_no_conflict`.
Extended by the next step, the SSO run so far is the start of a memory-DRF
trace (`prefix_agreement`). Since a pending write, its thread has taken part in
no primitive that orders memory, so happens-before cannot carry the write to
another thread (`hb_quiet`). The next access therefore cannot conflict with it:
a read never misses another thread's pending write, and two threads never hold
pending writes to the same location.

## Spec

Spec is SIMT-Step's speculative target. SSO fires a collective only when no
thread may still run it. Spec waits only for the threads known to run it,
those whose every path reaches it (`must_reach`). It does not wait for a thread
that may still take a branch away from the collective, which SIMT-Step calls
unknown; it bets that such a thread will not come. SIMT-Step discards a run in
which an unknown thread joins the collective's dynamic block after the firing.
We approximate this by letting Spec fire each instance at most once: a thread
that joins late waits at the collective forever, so the run never completes.
Firing before the unknown threads have decided is specific to Spec; under SSO
no thread can arrive after a firing. Thread steps and memory are those of SSO
with delayed visibility, so the two targets differ only in when a collective
may fire. In
`late`, each thread writes its own cell and then calls `AddZero` with no branch
in between, so Spec must wait for both threads (`late_waits`).

`spec_grouping_depends_on_schedule` shows that Spec conforms to neither
configuration. In `single_writer`, both threads read a flag and, when it is
zero, meet at `AddZero`; afterwards thread 0 sets the flag. The kernel is
WarpDRF for either configuration (`single_writer_conditions`): the reference
orders thread 1's read before thread 0's write through the collective
(`single_writer_memory_drf`), and both threads join it, so its group is the
whole warp. Under Spec, which threads join the collective depends on the
schedule:

- If thread 1 arrives in time, the collective fires with `[0; 1]`, and the run
  has the reference's trace and final memory (`single_writer_on_time`).
- If thread 0 fires it alone while thread 1 has not yet taken the branch, it
  then writes 1 (`single_writer_early`). The write stays pending, so thread 1
  reads 0, and its read races with the write (`early_trace_race`). The race
  aborts the run before thread 1 reaches the collective, so Spec's bet is never
  contradicted and SIMT-Step does not discard the run.

The theorem states both groups: `[0; 1]` in the reference and the first Spec
run, and `[0]` in the second, which races. So the collective has no fixed
group under Spec. `warpdrf_fails_under_spec` states the consequence: for
either configuration, the guarantee that `delayed_agreement` proves for SSO
with delayed visibility does not hold for Spec with the same memory.

## Examples

`Tests.v` computes reference traces and proves the group of an instance in
every completed execution for these kernels:

- nested sites and two independent halves of the warp;
- `partial`, where only thread 0 runs `AddZero`;
- `two_adds`, with two `AddZero`s in one thread's code under different labels;
- a `Break` from a conditional and a `Continue`, each of which excludes a thread
  from a barrier in its loop;
- threads that leave a loop in different iterations and meet after it;
- a barrier met by fewer threads in each iteration;
- nested loops.

It also proves thread 2's read in every completed execution of the relay. It
shows that crossed collectives never finish, and that a thread whose code
contains the same collective twice is rejected.

Two examples use primitive results and `sync`:

- `reduce`: each of three threads adds `tid + 1` with a reduction that does
  not order memory, and thread 0 stores the sum. Every completed execution ends
  with 6 in that cell (`reduce_result`).
- `handoff`: thread 0 writes a cell, both threads meet at a primitive, and
  thread 1 reads the cell. If the primitive orders memory, the kernel is
  memory-DRF and thread 1 reads 1 in every completed execution
  (`sync_handoff_reads`). If it does not, nothing orders the write before the
  read, and the reference trace is not memory-DRF (`nosync_handoff_race`).
  Under delayed visibility, thread 1's read in the unordered handoff misses
  the pending write and races with it, so the run aborts
  (`nosync_handoff_delayed_aborts`); the ordered one reads 1 in every
  finished run (`sync_handoff_delayed_reads`).
- `dot`: a primitive with two arguments; every completed execution stores the
  sum of `tid * (tid + 1)` over three threads, 8 (`dot_result`).
- `lone_full`: a primitive that requires the whole warp, run by thread 0
  alone; the structured partial configuration rejects the kernel
  (`lone_full_rejected`).

Three examples use the other statements:

- `doubled`: each thread computes `2 * tid` with a local statement and stores
  it (`doubled_result`).
- `early_return`: thread 1 returns before a barrier, which threads 0 and 2 then
  meet (`early_return_groups`).
- `switched`: each thread picks a barrier with a `Switch` on its thread
  identifier (`switch_groups`).

## Scope

| Area | Status |
| --- | --- |
| Memory | Sequentially consistent; no run races, and finished runs agree |
| Delayed visibility | After GPUVerify: a write reaches other threads once its thread takes part in a primitive that orders memory, and a race aborts the run (`Delayed.v`) |
| Warps | One warp; no workgroup of several warps and no workgroup barrier |
| Control flow | Nested conditionals, `Switch` as a chain of conditionals, structured loops with `Break` and `Continue`, and `Return` |
| Local state | `x := f(e, ...)` binds `x` over the code after it; a variable cannot be updated, so loop-carried values such as counters live in memory cells a thread owns |
| Primitives | Several arguments, results from an uninterpreted function of the participants' values, `ord(p)` as `sync`, and `req(p)` as `full` |

## Verification

- `Store.v`, `Code.v`: commuting memory effects, the thread step, its replay
  from an observation, and the swap of steps by different threads.
- `Model.v`: `reach` and its monotonicity under steps and releases.
- `Order.v`: the transitive happens-before and its preservation under swaps.
- `Commute.v`: commutation and persistence of actions.
- `Agree.v`: agreement for every completed SSO execution from reference memory
  DRF alone, a completion for every unfinished one, memory DRF of every run,
  reference-run soundness, and acceptance of every reference run by the
  `StructuredPartial` check.
- `Blocks.v`: at most one group per instance in any execution of a well-sited
  kernel.
- `Delayed.v`: with delayed visibility, from reference memory DRF alone, no
  run races and every finished run agrees.
- `Spec.v`: a kernel that is WarpDRF for either configuration, with two Spec
  runs with delayed visibility that form different groups, a finished one that
  agrees with the reference and one that races; the failure of the guarantee
  under Spec for either configuration; and Spec waiting for a thread known to
  reach a collective.
- `Tests.v`: the examples above.

```sh
dune build
rocq check -silent -Q _build/default/src Faial \
  Faial.Warp.Store Faial.Warp.Code Faial.Warp.Model Faial.Warp.Order \
  Faial.Warp.Commute Faial.Warp.Agree Faial.Warp.Blocks Faial.Warp.Delayed \
  Faial.Warp.Spec Faial.Warp.Tests
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
