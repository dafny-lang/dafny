// RUN: %dafny /compile:0 /typeSystemRefresh:1 /generalNewtypes:1 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type D<X> = set

type B0<Y> = (int, B1<Y>)
type B1<YY> = y: set | true

newtype NN<!Y3> = iset<Y3>
datatype B2<!Y2> = Something(NN<Y2>)

newtype OO<!Y5> = y: iset<Y5> | true
codatatype B3<!Y4> = Something(OO<Y4>)

method M<T>(s: set)
method N<W>() returns (s: set<W>)
function F<U>(s: set): U
function G<U>(x: U): set

method M'(s: set)
method N'() returns (s: set)
function F'(s: set): int
function G'(x: int): set
