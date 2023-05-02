// RUN: %baredafny resolve %args "%S/dfyconfig.toml" > "%t"
// RUN: %diff "%s.expect" "%t"

module Consumer {

  import opened Wrappers

  function MaybeInt(): Option<int> {
    Some(42)
  }

}