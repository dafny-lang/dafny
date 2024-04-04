// RUN: %resolve --library "%S/dfyconfig.toml" > "%t"
// RUN: %diff "%s.expect" "%t"

module ConsumerConsumer {
  import opened Consumer
  import opened Wrappers

  function UsesMaybeInt(): Option<int> {
    MaybeInt()
  }
}