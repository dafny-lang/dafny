// RUN: %testDafnyForEachResolver "%s"


method Try (a:int)
{
	forall
    ensures a == a
	{
	}
}







