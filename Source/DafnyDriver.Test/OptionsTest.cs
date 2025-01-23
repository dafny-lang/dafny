using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Invocation;
using System.CommandLine.Parsing;
using System.Diagnostics;
using System.IO.Pipelines;
using System.Reactive.Concurrency;
using System.Reflection;
using System.Text;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.JsonRpc.Client;
using OmniSharp.Extensions.JsonRpc.Serialization;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using XunitAssertMessages;
using Command = System.CommandLine.Command;

namespace DafnyDriver.Test;


public class OptionsTest {
  [Fact]
  public async Task RunFlagsOverride() {
    await TestCliRunArgs([], options => {
      Assert.True(options.DafnyVerify);
      Assert.True(options.Verify);
      return 0;
    });
    await TestCliRunArgs(["--no-verify"], options => {
      Assert.False(options.DafnyVerify);
      Assert.False(options.Verify);
      return 0;
    });
    await TestCliRunArgs(["--no-verify", "--bprint=-"], options => {
      Assert.True(options.DafnyVerify);
      Assert.False(options.Verify);
      return 0;
    });
    await TestCliRunArgs(["--no-verify", "--sprint=-"], options => {
      Assert.True(options.DafnyVerify);
      Assert.False(options.Verify);
      return 0;
    });
    await TestCliRunArgs(["--no-verify", "--pprint=-"], options => {
      Assert.True(options.DafnyVerify);
      Assert.False(options.Verify);
      return 0;
    });
  }

  private static async Task TestCliRunArgs(string[] cmdArgs, Func<DafnyOptions, int> optionsCallback) {
    var fullArgs = new string[] {
      "run"
    };
    fullArgs = fullArgs.Concat(cmdArgs).Concat(new string[] { "file.dfy" }).ToArray();
    var callbackCalled = false;
    var newOptionsCallback = (DafnyOptions options) => {
      callbackCalled = true;
      return optionsCallback(options);
    };
    Command cmd = RunCommand.Create(newOptionsCallback);
    var rootCommand = new RootCommand("Test root command");
    rootCommand.AddCommand(cmd);
    var builder = new CommandLineBuilder(rootCommand).UseDefaults();
    var parser = builder.Build();
    TextReader inputReader = new StringReader("");
    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var console = new WritersConsole(inputReader, outputWriter, errorWriter);
    var exitCode = await DafnyNewCli.ExecuteForParser(console, fullArgs, parser);
    Assert.Equal<object>("", errorWriter.ToString());
    Assert.Equal(0, exitCode);
    Assert.True(callbackCalled);
  }
}
