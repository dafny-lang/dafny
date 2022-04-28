# Dafny encoding of concurrent programs

This folder contains Dafny programs that verify concurrent code, using the [Locally Checked Invariants](https://doi.org/10.1007/978-3-642-14295-6_42) technique developed for [VCC – a verifier for concurrent C code](https://www.microsoft.com/en-us/research/project/vcc-a-verifier-for-concurrent-c/).

These programs are the result of various iterations. The number in the file name represents the order in which the programs were written.

| Program                         | Encoding style     | Recursive invariants | Special features                                                       | Timeout issues |
|---------------------------------|--------------------|----------------------|------------------------------------------------------------------------|----------------|
| `01-InnerOuter.dfy`             |                    | unsupported          |                                                                        | no             |
| `02-DoubleRead.dfy`             | atomic transitions | unsupported          |                                                                        | no             |
| `03-SimpleCounter.dfy `         | atomic transitions | unsupported          |                                                                        | no             |
| `04-LeastGreatest.dfy `         |                    |                      |                                                                        | no             |
| `05-RecInvariantCut.dfy`        | atomic transitions | supported            |                                                                        | no             |
| `06-ThreadOwnership.dfy`        | sequential code    | supported            | ownership                                                              | no             |
| `07-CounterThreadOwnership.dfy` | atomic transitions | supported            | ownership, volatile                                                    | no             |
| `08-CounterNoTermination.dfy`   | atomic transitions | supported            | ownership, volatile                                                    | no             |
| `09-CounterNoStateMachine.dfy`  | sequential code    | supported            | ownership, volatile, preemption                                        | yes            |
| `10-SequenceInvariant.dfy`      | sequential code    | supported            | ownership, volatile, preemption, transitivity                          | yes            |
| `11-MutexGuard2.dfy`            | sequential code    | supported            | ownership, volatile, preemption, transitivity, method calls            | no             |
| `12-MutexLifetime-long.dfy`     | sequential code    | supported            | ownership, volatile, preemption, transitivity, method calls, lifetimes | yes            |
| `12-MutexLifetime-short.dfy`    | sequential code    | supported            | ownership, volatile, preemption, transitivity, method calls, lifetimes | no             |

Columns:
- **Encoding style**: A concurrent method is encoded either to a state machine of atomic transitions or to sequential Dafny code. The state machine encoding verifies quickly but requires the user to provide an invariant for each program point. The sequential code encoding requires much less annotations but typically needs more time to verify.
- **Recursive invariants**: Whether (mutually) recursive single- and two-state class invariants are supported.
- **Special features**:
    - *ownership*: The encoding ensures that objects transitively owned by a thread cannot be modified by other threads. This is useful to frame objects across preemption points.
    - *volatile*: An exception to the ownership mechanism. Volatile fields are allowed to be modified by a thread even if their object is owned by a different thread.
    - *preemption*: The sequential code encoding can call a special `Preemption` method that havocs all fields that might be modified by the environment during a preemption.
    - *transitivity*: The encoding uses a transitive two-state invariant to define the ownership rules.
    - *method calls*: The program encodes method calls.
    - *lifetimes*: The encoding uses lifetimes inspired by the Rust language to reason about (de)allocation.
- **Timeout issues**: Whether there are still timeout issues in a method of the encoding. This usually signals that there is still something to fix (e.g. a quantifier instantiation is not triggered, a postcondition or loop invariant is not strong enough, a lemma call is missing etc).

Known issues:
* Due to an incompleteness, the verifier doesn't know that an instance of a class cannot implement traits that the class doesn't extend. Thus, this property is assumed in the programs that need it.
* Since three-state lemmas are not supported by Dafny, in many programs the transitivity of two-state predicates is checked in a method and is then carefully assumed where needed.
* The verification time of the latest programs is particularly high, probably due to quantifier instantiations. The `/proverOpt:O:smt.qi.eager_threshold=30` parameter helps reducing the search space. Still, reporting a verification error on incorrect programs usually requires an hour or more.
