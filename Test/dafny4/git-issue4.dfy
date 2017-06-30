// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


function method IntToChar(i:int):char
  requires 0 <= i < 10
{
  (48 + i) as char
}

function method CharToInt(i:char):int
  
{
  ((i) as int) - 48
}

method Main() {
  print IntToChar(8), "\n";
	print CharToInt('8'), "\n";
}
