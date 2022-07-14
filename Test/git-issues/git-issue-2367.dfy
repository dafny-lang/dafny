// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"

newtype IntSubset = i:int | true

method Main() {
  if 2 != (-6 as IntSubset % -4) as int {
    print 1 / 0;
  }
  if -2 != (-6 as IntSubset / 4) as int {
    print 1 / 0;
  }
}
