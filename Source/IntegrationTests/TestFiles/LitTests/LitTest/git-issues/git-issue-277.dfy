// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M(a: array<int>) {
	assert a[..true] == a[true..]; // error (x2): incorrect type
}
