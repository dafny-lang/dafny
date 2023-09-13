// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


type Empty = x: object | false witness *
type EmptyQ = x: object? | false witness *
type EmptyInt = x: int | false witness *
const x := null as Empty // Error
const xq := null as EmptyQ // Error
const i := 0 as EmptyInt // Error

type foo = x: object? | x != null witness *

function m(): foo {
  null // Error
}
