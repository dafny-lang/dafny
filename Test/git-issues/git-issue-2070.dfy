datatype D<A> = D(a: A)
type DT(==)<A> = D<A> // Error: A might not support ==

datatype D1<A> = D1(d: D<A>)
type D1T(==)<A> = D1<A> // Error: A might not support ==

datatype D2<A> = D1(d: D<D<A>>)
type D2T(==)<A> = D2<A> // Error: A might not support ==
