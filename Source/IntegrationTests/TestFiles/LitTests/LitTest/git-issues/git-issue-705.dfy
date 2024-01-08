// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation

datatype MyDataType = AAA {
 function toString(): int { 222 }
}

method Main() {
  var dt: MyDataType;
  print dt, " ", dt.toString(), "\n";
}

