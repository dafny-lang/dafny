// RUN: %dafny /compile:0 /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Try (a:int) 
{
	forall
    ensures a == a;
	{
	}
} 







