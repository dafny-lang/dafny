// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=false --general-newtypes=false --general-traits=legacy

// Note, these tests seem to be specific to the old type system. With the new type system,
// assignments that, in some way, involve a conversion from Number to Integer require an
// explicit "as" type conversion.

method Main() {
  var n: set<Number> := {};
  var s: set<Integer>;
  s := DoItWithAssignment(n);
  print |s|, " ";
  s := DoItWithPlainLet(n);
  print |s|, " ";
  s := DoItWithOptimizedLet(n);
  print |s|, " ";
  s := DoItViaFunctionBodyResult(n);
  print |s|, "\n";
}

trait Number {
  const value: int
}

class Integer extends Number {
  constructor(value: int) {
    this.value := value;
  }
}

method DoItWithAssignment(numbers: set<Number>) returns (integers00: set<Integer>)
  requires |numbers| == 0
{
  integers00 := numbers;
}

function DoItWithPlainLet(numbers: set<Number>): set<Integer>
  requires |numbers| == 0
{
  {} +
  var integers11: set<Integer> := numbers;
  integers11
}

function DoItWithOptimizedLet(numbers: set<Number>): set<Integer>
  requires |numbers| == 0
{
  var integers22: set<Integer> := numbers;
  integers22
}

function DoItViaFunctionBodyResult(numbers: set<Number>): set<Integer>
  requires |numbers| == 0
{
  numbers
}
