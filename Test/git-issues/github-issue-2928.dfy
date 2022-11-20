// RUN: %testDafnyForEachCompiler %s

method Main() {
  var c := '\0';
  assert c == 0 as char;
  expect c == 0 as char;

  var s := "\03";
  
  assert |s| == 2;
  expect |s| == 2;

  assert s[0] == 0 as char;
  expect s[0] == 0 as char;

  assert s[1] == '3';
  expect s[1] == '3';
}
