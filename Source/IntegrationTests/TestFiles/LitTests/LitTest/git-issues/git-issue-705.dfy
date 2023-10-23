// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --spill-translation

datatype MyDataType = AAA {
 function toString(): int { 222 }
}

method Main() {
  var dt: MyDataType;
  print dt, " ", dt.toString(), "\n";
}

