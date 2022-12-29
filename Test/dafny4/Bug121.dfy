// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Try (a:int, b:int, c:int)
{
	forall
    ensures a * c == a * c;
    ensures b * c == b * c;
	{
	}
}







