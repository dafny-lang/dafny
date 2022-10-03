// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
	
type DoesNotSupportEq = int -> int

type AlwaysSupportsEq<A> = int

datatype SupportsEqDespiteParameter =
  SupportsEq(a: AlwaysSupportsEq<DoesNotSupportEq>)

type T_SupportsEqDespiteParameter(==) =
  SupportsEqDespiteParameter
