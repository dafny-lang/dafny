using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;

namespace Microsoft.Dafny;

public interface ICommandSpec {

  IEnumerable<IOptionSpec> Options { get; }

  Command Create();

  void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context);
}