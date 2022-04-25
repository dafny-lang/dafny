type Opaque

datatype Box<A> = Box(A)
type BoxT(==)<A> = Box<A> // Error: A might not support equality
type BoxInt(==) = Box<int> // OK
type BoxBox(==)<A> = Box<Box<A>> // Error: A might not support equality
type BoxedOpaque(==) = Box<Opaque> // Error: Opaque doesn't support eq

datatype DBoxedOpaque = DBoxedOpaque(s: Box<Opaque>)
type DBoxedOpaqueT(==) = DBoxedOpaque // Error: s has ghost fields through Box<>
