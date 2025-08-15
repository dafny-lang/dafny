import opened Std.Wrappers

method Main() {
  var result: Result<int, string> := Success(42);
  print result, "\n";
}
