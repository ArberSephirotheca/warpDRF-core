# WarpDRF

Terminology for the reference contract and its implementation guarantees.

## Language

**Reference execution**:
The execution used to check the contract and determine the expected observations
for a program and input.

**Unambiguous participation**:
The reference execution's primitive groups meet the chosen configuration's
participation requirements, including where the configuration permits a
primitive to occur. This is a contract premise, not a statement that every
target execution already forms those groups.

**Warp-uniform control flow**:
Every thread takes the same branch around a primitive, whatever the input and
schedule. The full-warp configuration permits primitives only there.

**Conforming target**:
A target that forms the groups its configuration describes. Spec conforms to
the full-warp configuration but not to the structured partial one.

**Participant agreement**:
Target executions form the same primitive groups as the reference execution.
This is part of the contract's guarantee.

**Memory DRF**:
Every pair of conflicting accesses is ordered by synchronization and program
order in the execution being checked.
