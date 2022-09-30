using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface ICommandSpec {
  string Name { get; }

  string Description { get; }

  IEnumerable<IOptionSpec> Options { get; }

  void PostProcess(DafnyOptions dafnyOptions, Options options);
}