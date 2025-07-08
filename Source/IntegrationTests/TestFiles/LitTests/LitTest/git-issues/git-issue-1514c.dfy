// RUN: %testDafnyForEachCompiler "%s" -- --standard-libraries --relax-definite-assignment

import opened Std.Wrappers

method id<T>(r: T) returns (r2: T)  {
  r2 := r;
}

method test(s: string) returns (r: Option<string>) {
  r := None;
  var x :- id<Option<string>>(Some(s));
  r := Some(x);
}

method Main() {
  var x := test("ok");
  if x.Some? {
    print x.value, "\n";
  } else {
    print "None?!";
  }
}
