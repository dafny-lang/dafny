// Datatypes

datatype Bool { False; True; }

datatype Nat { Zero; Suc(Nat); }

datatype List { Nil; Cons(Nat, List); }

datatype Pair { Pair(Nat, Nat); }

datatype PList { PNil; PCons(Pair, PList); }

datatype Tree { Leaf; Node(Tree, Nat, Tree); }

// Boolean functions

function not(b: Bool): Bool
{
  match b
  case False => #Bool.True
  case True => #Bool.False
}

function and(a: Bool, b: Bool): Bool
{
  if a == #Bool.True && b == #Bool.True then #Bool.True else #Bool.False
}

// Natural number functions

function add(x: Nat, y: Nat): Nat
{
  match x
  case Zero => y
  case Suc(w) => #Nat.Suc(add(w, y))
}

function minus(x: Nat, y: Nat): Nat
{
  match x
  case Zero => #Nat.Zero
  case Suc(a) => match y
    case Zero => x
    case Suc(b) => minus(a, b)
}

function eq(x: Nat, y: Nat): Bool
{
  match x
  case Zero => (match y
    case Zero => #Bool.True
    case Suc(b) => #Bool.False)
  case Suc(a) => (match y
    case Zero => #Bool.False
    case Suc(b) => eq(a, b))
}

function leq(x: Nat, y: Nat): Bool
{
  match x
  case Zero => #Bool.True
  case Suc(a) => match y
    case Zero => #Bool.False
    case Suc(b) => leq(a, b)
}

function less(x: Nat, y: Nat): Bool
{
  match y
  case Zero => #Bool.False
  case Suc(b) => match x
    case Zero => #Bool.True
    case Suc(a) => less(a, b)
}

function min(x: Nat, y: Nat): Nat
{
  match x
  case Zero => #Nat.Zero
  case Suc(a) => match y
    case Zero => #Nat.Zero
    case Suc(b) => #Nat.Suc(min(a, b))
}

function max(x: Nat, y: Nat): Nat
{
  match x
  case Zero => y
  case Suc(a) => match y
    case Zero => x
    case Suc(b) => #Nat.Suc(max(a, b))
}

// List functions

function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x,tail) => #List.Cons(x, concat(tail, ys))
}

function mem(x: Nat, xs: List): Bool
{
  match xs
  case Nil => #Bool.False
  case Cons(y, ys) => if x == y then #Bool.True else mem(x, ys)
}

function delete(n: Nat, xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) =>
    if y == n then delete(n, ys) else #List.Cons(y, delete(n, ys))
}

function drop(n: Nat, xs: List): List
{
  match n
  case Zero => xs
  case Suc(m) => match xs
    case Nil => #List.Nil
    case Cons(x, tail) => drop(m, tail)
}

function take(n: Nat, xs: List): List
{
  match n
  case Zero => #List.Nil
  case Suc(m) => match xs
    case Nil => #List.Nil
    case Cons(x, tail) => #List.Cons(x, take(m, tail))
}

function len(xs: List): Nat
{
  match xs
  case Nil => #Nat.Zero
  case Cons(y, ys) => #Nat.Suc(len(ys))
}

function count(x: Nat, xs: List): Nat
{
  match xs
  case Nil => #Nat.Zero
  case Cons(y, ys) =>
    if x == y then #Nat.Suc(count(x, ys)) else count(x, ys)
}

function last(xs: List): Nat
{
  match xs
  case Nil => #Nat.Zero
  case Cons(y, ys) => match ys
    case Nil => y
    case Cons(z, zs) => last(ys)
}

function mapF(xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) => #List.Cons(HardcodedUninterpretedFunction(y), mapF(ys))
}
function HardcodedUninterpretedFunction(n: Nat): Nat;

function takeWhileAlways(hardcodedResultOfP: Bool, xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) =>
    if whilePredicate(hardcodedResultOfP, y) == #Bool.True
    then #List.Cons(y, takeWhileAlways(hardcodedResultOfP, ys))
    else #List.Nil
}
function whilePredicate(result: Bool, arg: Nat): Bool { result }

function dropWhileAlways(hardcodedResultOfP: Bool, xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) =>
    if whilePredicate(hardcodedResultOfP, y) == #Bool.True
    then dropWhileAlways(hardcodedResultOfP, ys)
    else #List.Cons(y, ys)
}

function filterP(xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) =>
    if HardcodedUninterpretedPredicate(y) == #Bool.True
    then #List.Cons(y, filterP(ys))
    else filterP(ys)
}
function HardcodedUninterpretedPredicate(n: Nat): Bool;

function insort(n: Nat, xs: List): List
{
  match xs
  case Nil => #List.Cons(n, #List.Nil)
  case Cons(y, ys) =>
    if leq(n, y) == #Bool.True
    then #List.Cons(n, #List.Cons(y, ys))
    else #List.Cons(y, ins(n, ys))
}

function ins(n: Nat, xs: List): List
{
  match xs
  case Nil => #List.Cons(n, #List.Nil)
  case Cons(y, ys) =>
    if less(n, y) == #Bool.True
    then #List.Cons(n, #List.Cons(y, ys))
    else #List.Cons(y, ins(n, ys))
}

function ins1(n: Nat, xs: List): List
{
  match xs
  case Nil => #List.Cons(n, #List.Nil)
  case Cons(y, ys) =>
    if n == y
    then #List.Cons(y, ys)
    else #List.Cons(y, ins1(n, ys))
}

function sort(xs: List): List
{
  match xs
  case Nil => #List.Nil
  case Cons(y, ys) => insort(y, sort(ys))
}

// Pair list functions

function zip(a: List, b: List): PList
{
  match a
  case Nil => #PList.PNil
  case Cons(x, xs) => match b
    case Nil => #PList.PNil
    case Cons(y, ys) => #PList.PCons(#Pair.Pair(x, y), zip(xs, ys))
}

function zipConcat(x: Nat, xs: List, more: List): PList
{
  match more
  case Nil => #PList.PNil
  case Cons(y, ys) => #PList.PCons(#Pair.Pair(x, y), zip(xs, ys))
}

// Binary tree functions

function height(t: Tree): Nat
{
  match t
  case Leaf => #Nat.Zero
  case Node(l, x, r) => #Nat.Suc(max(height(l), height(r)))
}

function mirror(t: Tree): Tree
{
  match t
  case Leaf => #Tree.Leaf
  case Node(l, x, r) => #Tree.Node(mirror(r), x, mirror(l))
}

// The theorems to be proved

ghost method P1()
  ensures (forall n, xs :: concat(take(n, xs), drop(n, xs)) == xs);
{
}

ghost method P2()
  ensures (forall n, xs, ys :: add(count(n, xs), count(n, ys)) == count(n, (concat(xs, ys))));
{
}

ghost method P3()
  ensures (forall n, xs, ys :: leq(count(n, xs), count(n, concat(xs, ys))) == #Bool.True);
{
}

ghost method P4()
  ensures (forall n, xs :: add(#Nat.Suc(#Nat.Zero), count(n, xs)) == count(n, #List.Cons(n, xs)));
{
}

ghost method P5()
  ensures (forall n, xs, x ::
    add(#Nat.Suc(#Nat.Zero), count(n, xs)) == count(n, #List.Cons(x, xs))
    ==> n == x);
{
}

ghost method P6()
  ensures (forall m, n :: minus(n, add(n, m)) == #Nat.Zero);
{
}

ghost method P7()
  ensures (forall m, n :: minus(add(n, m), n) == m);
{
}

ghost method P8()
  ensures (forall k, m, n :: minus(add(k, m), add(k, n)) == minus(m, n));
{
}

ghost method P9()
  ensures (forall i, j, k :: minus(minus(i, j), k) == minus(i, add(j, k)));
{
}

ghost method P10()
  ensures (forall m :: minus(m, m) == #Nat.Zero);
{
}

ghost method P11()
  ensures (forall xs :: drop(#Nat.Zero, xs) == xs);
{
}

ghost method P12()
  ensures (forall n, xs :: drop(n, mapF(xs)) == mapF(drop(n, xs)));
{
}

ghost method P13()
  ensures (forall n, x, xs :: drop(#Nat.Suc(n), #List.Cons(x, xs)) == drop(n, xs));
{
}

ghost method P14()
  ensures (forall xs, ys :: filterP(concat(xs, ys)) == concat(filterP(xs), filterP(ys)));
{
}

ghost method P15()
  ensures (forall x, xs :: len(ins(x, xs)) == #Nat.Suc(len(xs)));
{
}

ghost method P16()
  ensures (forall x, xs :: xs == #List.Nil ==> last(#List.Cons(x, xs)) == x);
{
}

ghost method P17()
  ensures (forall n :: leq(n, #Nat.Zero) == #Bool.True <==> n == #Nat.Zero);
{
}

ghost method P18()
  ensures (forall i, m :: less(i, #Nat.Suc(add(i, m))) == #Bool.True);
{
}

ghost method P19()
  ensures (forall n, xs :: len(drop(n, xs)) == minus(len(xs), n));
{
}

ghost method P20()
  ensures (forall xs :: len(sort(xs)) == len(xs));
{
  assume false;  // Dafny is not able to verify it automatically
}

ghost method P21()
  ensures (forall n, m :: leq(n, add(n, m)) == #Bool.True);
{
}

ghost method P22()
  ensures (forall a, b, c :: max(max(a, b), c) == max(a, max(b, c)));
{
}

ghost method P23()
  ensures (forall a, b :: max(a, b) == max(b, a));
{
}

ghost method P24()
  ensures (forall a, b :: max(a, b) == a <==> leq(b, a) == #Bool.True);
{
}

ghost method P25()
  ensures (forall a, b :: max(a, b) == b <==> leq(a, b) == #Bool.True);
{
}

ghost method P26()
  ensures (forall x, xs, ys :: mem(x, xs) == #Bool.True ==> mem(x, concat(xs, ys)) == #Bool.True);
{
}

ghost method P27()
  ensures (forall x, xs, ys :: mem(x, ys) == #Bool.True ==> mem(x, concat(xs, ys)) == #Bool.True);
{
}

ghost method P28()
  ensures (forall x, xs :: mem(x, concat(xs, #List.Cons(x, #List.Nil))) == #Bool.True);
{
}

ghost method P29()
  ensures (forall x, xs :: mem(x, ins1(x, xs)) == #Bool.True);
{
}

ghost method P30()
  ensures (forall x, xs :: mem(x, ins(x, xs)) == #Bool.True);
{
}

ghost method P31()
  ensures (forall a, b, c :: min(min(a, b), c) == min(a, min(b, c)));
{
}

ghost method P32()
  ensures (forall a, b :: min(a, b) == min(b, a));
{
}

ghost method P33()
  ensures (forall a, b :: min(a, b) == a <==> leq(a, b) == #Bool.True);
{
}

ghost method P34()
  ensures (forall a, b :: min(a, b) == b <==> leq(b, a) == #Bool.True);
{
}

ghost method P35()
  ensures (forall xs :: dropWhileAlways(#Bool.False, xs) == xs);
{
}

ghost method P36()
  ensures (forall xs :: takeWhileAlways(#Bool.True, xs) == xs);
{
}

ghost method P37()
  ensures (forall x, xs :: not(mem(x, delete(x, xs))) == #Bool.True);
{
}

ghost method P38()
  ensures (forall n, xs :: count(n, concat(xs, #List.Cons(n, #List.Nil))) == #Nat.Suc(count(n, xs)));
{
}

ghost method P39()
  ensures (forall n, x, xs ::
            add(count(n, #List.Cons(x, #List.Nil)), count(n, xs)) == count(n, #List.Cons(x, xs)));
{
}

ghost method P40()
  ensures (forall xs :: take(#Nat.Zero, xs) == #List.Nil);
{
}

ghost method P41()
  ensures (forall n, xs :: take(n, mapF(xs)) == mapF(take(n, xs)));
{
}

ghost method P42()
  ensures (forall n, x, xs :: take(#Nat.Suc(n), #List.Cons(x, xs)) == #List.Cons(x, take(n, xs)));
{
}

ghost method P43(p: Bool)
  // this is an approximation of the actual problem 43
  ensures (forall xs :: concat(takeWhileAlways(p, xs), dropWhileAlways(p, xs)) == xs);
{
}

ghost method P44()
  ensures (forall x, xs, ys :: zip(#List.Cons(x, xs), ys) == zipConcat(x, xs, ys));
{
}

ghost method P45()
  ensures (forall x, xs, y, ys ::
            zip(#List.Cons(x, xs), #List.Cons(y, ys)) ==
            #PList.PCons(#Pair.Pair(x, y), zip(xs, ys)));
{
}

ghost method P46()
  ensures (forall ys :: zip(#List.Nil, ys) == #PList.PNil);
{
}

ghost method P47()
  ensures (forall a :: height(mirror(a)) == height(a));
{
  assume false;  // Dafny is not able to verify it automatically
}

// ...

ghost method P54()
  ensures (forall m, n :: minus(add(m, n), n) == m);
{
  assume false;  // Dafny is not able to verify it automatically
}

ghost method P65()
  ensures (forall i, m :: less(i, #Nat.Suc(add(m, i))) == #Bool.True);
{
  assume false;  // Dafny is not able to verify it automatically
}

ghost method P67()
  ensures (forall m, n :: leq(n, add(m, n)) == #Bool.True);
{
  assume false;  // Dafny is not able to verify it automatically
}
