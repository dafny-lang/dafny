// RUN: %dafny /noNLarith /z3opt:pi.warnings=true /proverWarnings:1 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function GetIndexInSequence<T>(s:seq<T>, x:T) : int
	requires x in s;
	ensures  0 <= GetIndexInSequence(s, x) < |s|;
	ensures  s[GetIndexInSequence(s, x)] == x; {
		var i :| 0 <= i < |s| && s[i] == x;
		i
	} 



