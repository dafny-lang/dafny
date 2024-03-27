// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


method Try (a:int)
{
	forall
    ensures a == a
	{
	}
}







