# WarpDRF

Terminology for the reference contract and its implementation guarantees.

## Language

**Reference execution**:
The execution used to check the contract and determine the expected observations
for a program and input.

**Unambiguous participation**:
The reference execution's primitive groups meet the chosen configuration's
participation requirements. The full-warp configuration requires every executed
primitive to include the complete warp. This is a contract premise, not a
statement that every target execution already forms those groups.

**Warp-uniform control flow**:
Every thread takes the same branch around a primitive. Placing primitives there
is how a programmer meets the full-warp configuration; branches that contain
no primitive may still diverge.

**Conforming target**:
A target that forms the groups its configuration describes. Spec, which fires a
collective without waiting for threads that may still branch away from it,
conforms to neither configuration: which threads join depends on the schedule.

**Participant agreement**:
Target executions form the same primitive groups as the reference execution.
This is part of the contract's guarantee.

**Memory DRF**:
Every pair of conflicting accesses is ordered by synchronization and program
order in the execution being checked.

**Collective site**:
The name of a warp collective in the kernel's code. A kernel is well-sited
when no thread's code names a site twice.

**Collective instance**:
A site together with the iteration counts of the loops around it. An instance
names one dynamic block; in loop-free code it is just the site.

**Unknown thread**:
For a collective instance, a thread that may still reach the instance but has
not arrived. SSO releases an instance only when no thread is unknown for it.
