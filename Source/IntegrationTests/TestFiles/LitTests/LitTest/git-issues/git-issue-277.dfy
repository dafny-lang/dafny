// RUN: %exits-with 2 %dafny /compile:3 /optimize "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m(a : array<int>) {
	assert a[..true] == a[..true];
}
