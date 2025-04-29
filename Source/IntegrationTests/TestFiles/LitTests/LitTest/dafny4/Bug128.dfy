// RUN: %verify --disable-nonlinear-arithmetic --solver-option="O:pi.warnings=true" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function GetIndexInSequence<T>(s:seq<T>, x:T) : int
	requires x in s
	ensures  0 <= GetIndexInSequence(s, x) < |s|
	ensures  s[GetIndexInSequence(s, x)] == x {
		var i :| 0 <= i < |s| && s[i] == x;
		i
	}



