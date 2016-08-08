// RUN: %dafny /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NativeTypes {
  newtype uint64 = int
} 

module ConversionModule {
  import opened NativeTypes

  predicate method Uint64ToBytes(u:uint64) { true }
}

abstract module AppStateMachine_s {
  import opened NativeTypes
}

module AppStateMachine_i refines AppStateMachine_s {
  import ConversionModule

  predicate method F(response:uint64)
  {
    ConversionModule.Uint64ToBytes(response)
  }
}
