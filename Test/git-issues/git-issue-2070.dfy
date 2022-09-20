datatype A<T> = A(T)

datatype B<T> = B(A<A<T>>)

type C(==)<T> = B<T> 
