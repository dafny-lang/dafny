// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NativeTypes {
  newtype uint64 = int
}

module ConversionModule {
  import opened NativeTypes

  compiled predicate Uint64ToBytes(u:uint64) { true }
}

abstract module AppStateMachine_s {
  import opened NativeTypes
}

module AppStateMachine_i refines AppStateMachine_s {
  import ConversionModule

  compiled predicate F(response:uint64)
  {
    ConversionModule.Uint64ToBytes(response)
  }
}

method Main() {
  var a := ConversionModule.Uint64ToBytes(67);
  var b := AppStateMachine_i.ConversionModule.Uint64ToBytes(67);
  var c := AppStateMachine_i.F(67);
  print a, " ", b, " ", c, "\n";
}
