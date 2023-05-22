// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs /spillTargetCode:3 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js /spillTargetCode:3 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go /spillTargetCode:3 "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java /spillTargetCode:3 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype MyDataType = AAA {
 function toString(): int { 222 }
}

method Main() {
  var dt: MyDataType;
  print dt, " ", dt.toString(), "\n";
}

