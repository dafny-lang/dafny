// RUN: %testDafnyForEachResolver "%s"


method {:extern "test"} testInt(i: int)
method {:extern "test"} testBool(b: bool) // Previously the verifier reported a name collision
