// RUN: %testDafnyForEachResolver "%s" -- --allow-axioms=false

type Even = x: int | x % 2 == 0
opaque const ten: Even := 10

const twoHundred: LessThanHundredNinetyNine := 200
const hundredNinetyNine: int := twoHundred as int - 1
type LessThanHundredNinetyNine = k | 0 <= k < hundredNinetyNine