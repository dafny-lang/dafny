datatype D<A> = D(a: A)
type DT(==)<A> = D<A> // Error: A might not support ==
datatype D'<A> = d'(d: D<D<A>>)
type D'T(==)<A> = D'<A> // Incorrectly accepted
