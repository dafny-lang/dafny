// NONUNIFORM: Rust-specific tests
// RUN: %baredafny build --target=rs --enforce-determinism --general-traits=legacy "%s"
// If there is no '#[inline(never)]' in front of ::dafny_runtime::increment_strong_count
// then the release will think it's safe to remove the strong count increment, resulting ins a segfault
// RUN: "%S/cargoreleasefailure-rust/cargo" run --release

module  TraitModule {
  trait {:termination false} MyTrait {
    method DoThing ( input: int ) returns (output: int)
  }
}

module ImplModule {
  import TraitModule
  class MyImpl extends TraitModule.MyTrait {
    constructor(){}
    method DoThing ( input: int ) returns (output: int)
    {
      return 1;
    }
  }
}

module WorkModule {
  import ImplModule
  import TraitModule

  method DoWork() {
    var worker := new ImplModule.MyImpl();
    DoMoreWork(worker, 1);
    DoMoreWork(worker, 2);
    DoMoreWork(worker, 3);
    DoMoreWork(worker, 4);
    DoMoreWork(worker, 5);
  }

  method DoMoreWork(client : TraitModule.MyTrait, num : int)
  {
    var _ := client.DoThing(num);
  }
}

module MainModule {
  import WorkModule
  method Main() {
    WorkModule.DoWork();
  }
}
