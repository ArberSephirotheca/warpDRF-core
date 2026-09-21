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

## Connection to the contract

`Contract.v` fixes a reference run for the litmus: thread 0 runs to the
collective, thread 1 runs to it, and after the collective they finish in that
order. Its trace and participant group are proved to arise from a completed
execution, not just assumed. This is one example of the paper's reference
scheduling discipline, not a general reference scheduler.

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
Spec. They are not a general proof that `conditions` implies reference agreement.

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

```sh
dune build
rocq check -silent -Q _build/default/src Faial \
  Faial.Warp.Semantics Faial.Warp.Examples Faial.Warp.Handoff \
  Faial.Warp.Participation Faial.Warp.Speculation Faial.Warp.Contract
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
