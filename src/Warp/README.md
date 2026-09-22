# Independent-execution baseline

`Lang.v` contains reads, writes, sequencing, conditionals, labeled warp barriers,
and a zero-contribution collective. It uses Faial's expressions and read-binding
rules. A separate syntax lets us add barriers without changing upstream Faial
definitions.
`Semantics.v` reuses Faial's memory and access records. A state holds shared
memory and one remaining program per thread; list indices are thread identifiers.
Writes are immediately visible. A fixed `input` function supplies initial values.
Traces record memory accesses and their values.

For a fixed positive width `W`, warp `q` contains threads `q*W` through
`q*W+W-1`. Schedules contain `Thread tid` for ordinary steps and `Sync q` for
joint barrier steps. `Sync q` succeeds only if all `W` threads exist and are
waiting at the same barrier label. It consumes exactly one barrier per thread
and leaves other warps' programs unchanged. Repeated uses of a label are consumed
in successive joint steps, so a thread cannot run ahead to a later occurrence.
Barriers do not change memory in this sequentially consistent model.

`advance` performs one action; `execution` permits any successful action;
`run` follows a supplied schedule. `run_sound` and `run_complete` connect them.
`None` means the selected action cannot execute, not that the kernel has
terminated. Only `finished` identifies termination; exhausting a schedule does
not. Waiting threads need not be selected, and no fairness is assumed.

## Bounded participation and speculation

`Participation.v` adds one conditional per thread and one collective in its true
branch, for a single warp. `AddZero` represents `subgroupAdd(0)` with its unused
zero result; it is distinct from the full-warp `Barrier`. For this experiment,
both policies give the collective memory ordering among its actual participants.
This is a choice of abstract semantics, not a claim about every real subgroup
intrinsic. The model calls `thread_step` directly for ordinary operations;
collective execution is a separate joint step.

Each thread's branch decision is `Unresolved`, `Entered`, or `Skipped`. A
collective requires all `Entered` threads to arrive and records their thread
identifiers. The two policies differ only in handling unresolved threads:

- `SSO` waits for every thread's branch decision. A partial group is allowed
  when the other threads have decided to skip it.
- `Spec` can execute while decisions remain unresolved, predicting those
  threads will skip it. A later decision to enter is rejected. Successful
  termination requires every thread to finish and every decision to be
  resolved, so an unfinished speculative prefix is not a validated execution.

The trace records `Memory` events and `Synchronize group` events. A collective
orders accesses before it against accesses after it only when both accessing
threads belong to `group`. It does not order two accesses on the same side, or
an access by an excluded thread. `memory_events` projects out synchronization
events when comparing memory values.

`Speculation.v` adapts the two-thread example from SIMT-Step's `speculate.tex`,
with `x` initially zero:

```c
int cond = load(x);
if (cond == 0) {
    subgroupAdd(0);
    store(x, 1);
}
```

Every terminating `SSO` execution reads zero in both threads and records
participants `[0; 1]`. A validated `Spec` execution instead records `[0]`:
thread 0 reads zero, executes the collective, and writes one; thread 1 then
reads one and skips the branch. Both executions end with `x = 1`, so the
distinguishing observations are the reads and participants, not final memory.
The symmetric singleton group and the full group are also permitted by `Spec`.

The original uses atomic accesses. This adaptation uses ordinary SC accesses,
so its race classification does not apply to the original atomic program.

Nested branches, loops, repeated collective instances, full dynamic-block
semantics, and weak memory remain out of scope. This is a bounded instantiation
of SIMT-Step's SSO/Spec distinction, not a complete implementation of either.

## Deterministic reference execution

`Reference.supported` defines the initial fragment: a nonempty list of thread
programs, each with exactly one conditional, one collective in its true branch,
and none in its false branch. All collective calls denote one common abstract
site. Ordinary reads, writes, and sequencing may surround the conditional and
collective. Nested or repeated conditionals, additional
collectives, and full-warp barriers are rejected. This checks program structure,
not variable binding; an unresolved expression can still prevent execution.

`Reference.run input programs` runs the lowest-numbered runnable thread until
it waits or finishes, then selects the next. When no thread can advance alone,
it attempts the SSO collective step. It reuses the existing transitions and
returns `Some (trace, last)` only when `Participation.finished` holds. The
function also executes racy programs; checking memory DRF remains separate.

The evaluator's step bound is derived from syntax size. `advance_decreases`
proves that every successful step decreases this measure, including collective
steps. `Reference.run_sound` proves that success is a completed SSO execution
of an in-fragment program. `Reference.run_failure` proves that failure on an
in-fragment program reaches an unfinished state with no enabled action: it
cannot be caused by insufficient fuel.

## Connection to the contract

`Contract.v` retains the explicit reference traces for both litmus programs.
`ReferenceExamples.v` proves that the reference scheduler reproduces them.

The memory-DRF condition reuses Faial's `Conflict` definition. Every conflicting pair
must have a collective between its accesses, with both threads in that
collective's recorded group. This gives the cross-thread happens-before check
for the bounded fragment with at most one collective. `Hist.Safe` remains a
special case: a trace with no conflicting accesses is memory-DRF without using
the collective's ordering. Multiple collective instances and general
happens-before chains are not implemented by this check.

`conditions` conjoins reference memory DRF with `ParticipationGuaranteed`:
every completed execution under the selected policy must preserve the reference
group. This is a logical property, not a static checker or a reference-only
participation test. The two-writer adaptation fails reference memory DRF:
both writes follow the collective and remain unordered.

The separately named `single_writer` variant removes only thread 1's store.
Both threads still load `x` and conditionally execute the collective; only
thread 0 writes afterward. The programs are supplied per thread, so no nested
conditional is added to the bounded semantics. Its results are:

| Check | SSO | Spec |
| --- | --- | --- |
| Memory DRF of the same reference trace | Holds | Holds |
| Every completed execution preserves the reference group `[0; 1]` | Holds | Fails |
| Thread 0 and thread 1 read values | Always `0, 0` | `0, 1` is also possible |

The reference collective orders thread 1's read before thread 0's write. In the
speculative execution, only thread 0 participates; the collective therefore
does not order its write against thread 1's later read. The speculative trace
has a memory race despite both policies supplying participant-scoped ordering.

`single_writer_reference_memory_drf`, `single_writer_sso_conditions`, and
`single_writer_spec_not_conditions` connect the example to the contract.
`single_writer_sso_all_executions` proves reference read values, participation,
and the final value of `x` for all completed SSO executions;
`single_writer_spec_validated` supplies the differing speculative execution.
These example-specific proofs show that the SSO guarantee does not transfer to
Spec. The general result for the supported SSO fragment is described below.

## SSO agreement proof

`same_observations` compares participant groups, each thread's ordered read
history (including addresses and values), and the final value at every memory
location. It does not require the same global event order or the same internal
representation of the memory map.

`Agreement.sso_agreement` proves `SSOAgreement`: for every input and supported
program with a successful reference run, the two contract conditions imply
matching observations for every completed SSO execution. The proof uses the
existing transitions without changing either execution policy:

1. `Commutation.v` proves that nonconflicting steps by different threads can be
   swapped while preserving their observations and continuations. A collective
   and an ordinary step enabled together commute because that thread is outside
   the collective. Memory maps are compared by their values, not their tree shape.
2. `TraceOrder.v` proves that the permitted swaps preserve memory DRF and each
   thread's read history, including synchronization ordering for participants.
3. `Agreement.pull_enabled` moves the target's next action to the front of the
   reference execution. Repeating this aligns the executions without assuming
   that every target schedule is already DRF.

The stronger `completed_sso_agreement` theorem only needs the reference run to
be memory-DRF. In this bounded SSO model, waiting for all branch decisions also
preserves the reference participant group. `sso_participation_guaranteed` derives
that guarantee, and `sso_memory_drf` proves that completed target traces remain
memory-DRF. Neither conclusion extends to Spec: the single-writer counterexample
has a completed speculative execution with different reads and participants.

The result covers the supported single-warp, single-collective fragment above,
with ordinary SC accesses and the zero-result collective. It does not add loops,
general dynamic blocks, additional primitives, delayed visibility, or a progress
guarantee for target executions.

## Verification

- `Semantics.v`: matching full-warp barriers, unchanged memory and other warps,
  thread counts, and equivalence of schedules and the execution relation.
- `Examples.v`: SC reads/writes, invalid steps, mismatched and repeated barriers,
  a 32-thread release, and cross-warp handoffs that can read old or new values.
- `Handoff.v`: every completed schedule of a two-thread synchronized handoff
  reads the written value, for any initial memory.
- `Participation.v`: schedule/execution equivalence and rejection of late
  participants after speculative execution.
- `Speculation.v`: all completed SSO schedules for both examples, differing
  completed Spec schedules, and inability to finish with a wrong prediction.
- `Contract.v`: reference runs, memory-DRF classifications, participant-scoped
  ordering, and the SSO/Spec contract distinction for the single-writer example.
- `Reference.v`: decreasing syntax size, a complete action search, successful-run
  soundness, and failure reaching a stuck state rather than exhausting fuel.
- `ReferenceExamples.v`: the existing litmus traces, input-dependent and partial
  participation, 32 threads, rejected programs, unresolved expressions, and
  read-history comparisons that ignore interleaving but preserve read values;
  an all-input handoff with a data-dependent address, nonparticipant execution
  across a collective, distinct map shapes with equal values, and Spec disagreement.
- `Commutation.v`: memory replay, execution transport across equal memory values,
  ordinary and collective step swaps, and preservation of enabled actions.
- `TraceOrder.v`: preservation of memory DRF and read histories under permitted swaps.
- `Agreement.v`: agreement for every completed SSO execution, participation
  preservation, and memory-DRF preservation.

```sh
dune build
rocq check -silent -Q _build/default/src Faial \
  Faial.Warp.Semantics Faial.Warp.Examples Faial.Warp.Handoff \
  Faial.Warp.Participation Faial.Warp.Speculation Faial.Warp.Contract \
  Faial.Warp.Reference Faial.Warp.TraceOrder Faial.Warp.Commutation \
  Faial.Warp.Agreement Faial.Warp.ReferenceExamples
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
