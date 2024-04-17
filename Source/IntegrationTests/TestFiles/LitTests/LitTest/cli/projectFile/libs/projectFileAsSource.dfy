// RUN: %resolve "%S/projectFileAsSource.dfyconfig.toml" --allow-warnings --function-syntax 3 > "%t"
// RUN: ! %resolve "%S/projectFileAsSource.dfyconfig.toml" --allow-warnings --function-syntax 3 --unicode-char false >> "%t"
// RUN: %diff "%s.expect" "%t"

module ConsumerConsumer {
  import opened Consumer
  import opened Wrappers

  function method UsesMaybeInt(): Option<int> {
    MaybeInt()
  }
}