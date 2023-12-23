// RUN: %testDafnyForEachResolver --expect-exit-code 2 "%s"


const x: MyInt := 200
const y: int := x as int + 180
newtype MyInt = k | 0 <= k < y
