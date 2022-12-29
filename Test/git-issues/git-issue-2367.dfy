// RUN: %baredafny run %args --no-verify --target=cs "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"

newtype IntSubset = i:int | true

method Main() {
  if 2 != (-6 as IntSubset % -4) as int {
    print 1 / 0;
  }
  if -2 != (-6 as IntSubset / 4) as int {
    print 1 / 0;
  }
}
