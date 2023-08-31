// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

datatype D = D(q:int, r:int, s:int, t:int)

method Main()
{
    print D(10, 20, 30, 40);
    print "\n";
}
