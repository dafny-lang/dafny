// RUN: ! %testDafnyForEachResolver "%s" -- --allow-axioms=false

type Even = x: int | x % 2 == 0
opaque const ten: Even := 10

const twoHundred: LessThanTwoHundred := 200
type LessThanTwoHundred = k | 0 <= k < twoHundred

const twoHundred_2: LessThanHundredNinetyNine := 200
const hundredNinetyNine: int := twoHundred_2 as int - 1
type LessThanHundredNinetyNine = k | 0 <= k < hundredNinetyNine