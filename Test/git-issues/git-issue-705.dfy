// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment /spillTargetCode:3

datatype MyDataType = AAA {
 function toString(): int { 222 }
}

method Main() {
  var dt: MyDataType;
  print dt, " ", dt.toString(), "\n";
}

