using System;
using System.CommandLine;
using System.IO;
using System.Threading.Tasks;
using DafnyDriver.Commands;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public class ResourceCommand {
  public static Command Create() {
    var result = new Command("resource", "Output a resource file from the Dafny distribution.");
    result.IsHidden = true;
    result.AddArgument(ResourceName);
    result.AddArgument(OutputPath);

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => OutputResource(options));
    return result;
  }
  
  private static readonly Argument<string> ResourceName = new("The name of the resource to output.");
  private static readonly Argument<FileInfo> OutputPath = new("The path to output the resource to.");

  private static async Task<int> OutputResource(DafnyOptions options) {
    var resourceName = options.Get(ResourceName);
    var outputPath = options.Get(OutputPath);

    var assembly = System.Reflection.Assembly.Load("DafnyPipeline");
    var stream = assembly.GetManifestResourceStream(resourceName);
    if (stream is null) {
      await options.OutputWriter.Status($"Cannot find embedded resource: {resourceName}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var rd = new StreamReader(stream);
    await using var writer = outputPath.CreateText();
    SinglePassCodeGenerator.WriteFromStream(rd, writer);

    return 0;
  }
}