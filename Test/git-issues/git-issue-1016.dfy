// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = Some(value: T) | None {
  predicate method IsFailure() {
    None?
  }
  function method PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }
  function method Extract(): T
    requires Some?
  {
    value
  }
}

type Process(==)

type State(==)

datatype Event = Event(process: Process, state: State)

function method Find(process: Process, log: seq<Event>): (r: Option<nat>)
  ensures r.Some? ==> r.value < |log|

function method Gimmie(): Option<int>

method Test0(process: Process, m: map<Process, State>, log: seq<Event>)
  requires process in m.Keys
{
  // x has type Option<State>
  var x :=
    Some(m[process]);
  // y has type Option<Process>
  var y :=
    var L := Find(process, log);
    if L == None then None else Some(log[L.value].process);
  // z's RHS is a different way of writing y's RHS
  // so, z also has type Option<Process>
  var z :=
    var last :- Find(process, log);
    Some(log[last].process);

  // Without the type errors in the other methods, the following assertion
  // type checks and verifies.
  assert y == z;
}

method Test1(process: Process, m: map<Process, State>, log: seq<Event>)
  requires process in m.Keys
{
  // The definitions of x, y, and z are exactly like in Test0
  var x :=
    Some(m[process]);
  var y :=
    var L := Find(process, log);
    if L == None then None else Some(log[L.value].process);
  var z :=
    var last :- Find(process, log);
    Some(log[last].process);

  // The following line gives the expected type error
  var b := x == y;  // error: incompatible types Option<State> and Option<Process>
}

method Test2(process: Process, m: map<Process, State>, log: seq<Event>)
  requires process in m.Keys
{
  // The definitions of x, y, and z are exactly like in Test0
  var x :=
    Some(m[process]);
  var y :=
    var L := Find(process, log);
    if L == None then None else Some(log[L.value].process);
  var z :=
    var last :- Find(process, log);
    Some(log[last].process);

  var c := x == z;  // ERROR: this should give a type error
}

method Test3(process: Process, m: map<Process, State>, log: seq<Event>)
  requires process in m.Keys
{
  // The definitions of x, y, and z are like in Test0, except the types are given
  // explicitly here.
  var x: Option<State> :=
    Some(m[process]);
  var y: Option<Process> :=
    var L := Find(process, log);
    if L == None then None else Some(log[L.value].process);
  var z: Option<Process> :=
    var last :- Find(process, log);
    Some(log[last].process);

  // With the explicit types above, the assignments above type check, and
  // the following line gives the expected type error.
  var c := x == z;  // error: incompatible types Option<State> and Option<Process>
}

method Test4(process: Process, m: map<Process, State>, log: seq<Event>)
  requires process in m.Keys
{
  // The definitions of x, y, and z are exactly like in Test0
  var x :=
    Some(m[process]);
  var y :=
    var L := Find(process, log);
    if L == None then None else Some(log[L.value].process);
  var z :=
    var last :- Find(process, log);
    Some(100);

  var c := x == z;  // ERROR: this should give a type error
}

method Test5(s: State)
{
  // The definitions of x, y, and z are exactly like in Test0
  var x :=
    Some(s);
  var z :=
    var n :- Gimmie();
    Some(100.0);

  var c := x == z;  // ERROR: this should give a type error
}

