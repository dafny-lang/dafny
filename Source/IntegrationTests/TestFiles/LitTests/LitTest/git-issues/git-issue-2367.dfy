// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

newtype IntSubset = i:int | true

method Main() {
  if 2 != (-6 as IntSubset % -4) as int {
    print 1 / 0;
  }
  if -2 != (-6 as IntSubset / 4) as int {
    print 1 / 0;
  }
}
