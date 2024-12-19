// RUN: %resolve "%S/dfyconfig.toml" --allow-warnings > "%t"
// RUN: %diff "%s.expect" "%t"

module Consumer {

  import opened Wrappers

  function MaybeInt(): Option<int> {
    Some(42)
  }

  method AssertFalse() ensures false { } 
}