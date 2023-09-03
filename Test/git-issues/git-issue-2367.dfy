// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

newtype IntSubset = i:int | true

method Main() {
  if 2 != (-6 as IntSubset % -4) as int {
    print 1 / 0;
  }
  if -2 != (-6 as IntSubset / 4) as int {
    print 1 / 0;
  }
}
