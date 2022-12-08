// RUN: %dafny /compile:3 /optimize /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m(a : array<int>) {
	assert a[..true] == a[..true];
}
