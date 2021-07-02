// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype PhantomData<T> = PhantomData(ghost value: T)

method Test0(t0: (ghost int)) { print "Test0: ", t0, "\n"; }
method Test1(t1: (ghost int, int)) { print "Test1: ", t1, "\n"; }
method Test2(t2: (int, ghost int, int)) { print "Test2: ", t2, "\n"; }
method Test3(t3: ((ghost int), (ghost int, int), ghost int)) { print "Test3: ", t3, "\n"; }

method Main() {
    var p := PhantomData(123);
    var t0 := (ghost 00);
    var t1 := (ghost 11, 22);
    var t2 := (33, ghost 44, 55);
    var t3 := ((ghost 66), (ghost 77, 88), ghost 99);
    Test0(t0);
    Test1(t1);
    Test2(t2);
    Test3(t3);
}
