// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


method Try (a:int, b:int, c:int)
{
	forall
    ensures a * c == a * c
    ensures b * c == b * c
	{
	}
}







