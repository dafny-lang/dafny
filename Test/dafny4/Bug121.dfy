// RUN: %testDafnyForEachResolver "%s"


method Try (a:int, b:int, c:int)
{
	forall
    ensures a * c == a * c
    ensures b * c == b * c
	{
	}
}







