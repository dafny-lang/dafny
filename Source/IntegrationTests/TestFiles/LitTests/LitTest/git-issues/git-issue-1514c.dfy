// RUN: %verify "%s" --standard-libraries:true  > "%t"
// RUN: %diff "%s.expect" "%t"

import opened DafnyStdLibs.Wrappers

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
