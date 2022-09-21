// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
	
datatype A<T> = A(T)

datatype B<T> = B(A<A<T>>)

type C(==)<T> = B<T> 
