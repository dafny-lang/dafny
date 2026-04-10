using System;
using System.Collections.Generic;
using System.CommandLine;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.JsonRpc.Testing;
using OmniSharp.Extensions.LanguageProtocol.Testing;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Server;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Various;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Client;
using Xunit;
using Xunit.Abstractions;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace Microsoft.Dafny.LanguageServer.IntegrationTest {
  public class DafnyLanguageServerTestBase : LanguageProtocolTestBase {

    protected readonly string SlowToVerify = @"
lemma {:resource_limit 100000} SquareRoot2NotRational(p: nat, q: nat)
  requires p > 0 && q > 0
  ensures (p * p) !=  2 * (q * q)
{ 
  if (p * p) ==  2 * (q * q) {
    calc == {
      (2 * q - p) * (2 * q - p);
      4 * q * q + p * p - 4 * p * q;
      {assert 2 * q * q == p * p;}
      2 * q * q + 2 * p * p - 4 * p * q;
      2 * (p - q) * (p - q);
    }
  }
}".TrimStart();

    protected string SlowToVerifyNoLimit => SlowToVerify.Replace(" {:resource_limit 100000}", "");

    protected readonly string NeverVerifies = @"
lemma {:neverVerify} HasNeverVerifyAttribute(p: nat, q: nat)
  ensures true
{
}".TrimStart();

    public const string LanguageId = "dafny";
    protected static int fileIndex;
    protected readonly TextWriter output;
    protected readonly ILogger logger;

    public ILanguageServer Server { get; protected set; }

    public IProjectDatabase Projects => Server.GetRequiredService<IProjectDatabase>();

    protected DafnyLanguageServerTestBase(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information)
      : base(new JsonRpcTestOptions(CreateLoggerFactory(dafnyLogLevel))) {
      this.output = new WriterFromOutputHelper(output);
      logger = CreateLoggerFactory(dafnyLogLevel).CreateLogger("default");
    }

    private static ILoggerFactory CreateLoggerFactory(LogLevel dafnyLogLevel) {
      return LoggerFactory.Create(
        builder => {
          builder.AddFilter("OmniSharp.Extensions.JsonRpc", LogLevel.None);
          builder.AddFilter("OmniSharp", LogLevel.Warning);
          builder.AddFilter("Microsoft.Dafny", dafnyLogLevel);
          builder.AddConsole();
        });
    }

    protected virtual void ServerOptionsAction(LanguageServerOptions serverOptions) {
    }

    protected Task<(ILanguageClient client, ILanguageServer server)> Initialize(Action<LanguageClientOptions> clientOptionsAction, Action<DafnyOptions> serverOptionsAction) {
      /*
       * I would rather use LanguageServerOptions.RegisterForDisposal, but it doesn't seem to work
       * Alternatively one can do Disposable.Add((IDisposable)Server.Services), but we've seen many
       * ObjectDisposedExceptions in tests that might relate to this, so let's be more specific and only dispose
       * IProjectDatabase
       */
      Disposable.Add(new AnonymousDisposable(() => {
        var database = Server.Services.GetRequiredService<IProjectDatabase>();
        database.Dispose();
      }));
      return base.Initialize(clientOptionsAction, GetServerOptionsAction(serverOptionsAction));
    }

    private sealed class AnonymousDisposable : IDisposable {
      private Action action;

      public AnonymousDisposable(Action action) {
        this.action = action;
      }

      public void Dispose() => Interlocked.Exchange(ref action, null)?.Invoke();
    }

    private Action<LanguageServerOptions> GetServerOptionsAction(Action<DafnyOptions> modifyOptions) {
      var dafnyOptions = DafnyOptions.CreateUsingOldParser(output);
      dafnyOptions.Set(ProjectManager.UpdateThrottling, 0);
      dafnyOptions.Set(CachingProjectFileOpener.ProjectFileCacheExpiry, 0);
      modifyOptions?.Invoke(dafnyOptions);
      dafnyOptions.UsingNewCli = true;
      LanguageServer.ConfigureDafnyOptionsForServer(dafnyOptions);
      ApplyDefaultOptionValues(dafnyOptions);
      return options => {
        options.WithDafnyLanguageServer(dafnyOptions, () => { });
        options.Services.AddSingleton(dafnyOptions);
        options.Services.AddSingleton<IProgramVerifier>(serviceProvider => new SlowVerifier(
          serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>()
        ));
        ServerOptionsAction(options);
      };
    }

    private static void ApplyDefaultOptionValues(DafnyOptions dafnyOptions) {
      var testCommand = new System.CommandLine.Command("test");
      foreach (var serverOption in LanguageServer.Options) {
        testCommand.AddOption(serverOption);
      }

      var result = testCommand.Parse("test");
      foreach (var option in LanguageServer.Options) {
        if (!dafnyOptions.Options.OptionArguments.ContainsKey(option)) {
          var value = result.GetValueForOption(option);

          dafnyOptions.SetUntyped(option, value);
        }

        dafnyOptions.ApplyBinding(option);
      }
    }

    protected static string GetFreshTempPath() {
      return Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    }

    protected static TextDocumentItem CreateTestDocument(string source, string filePath = null, int version = 1) {
      DocumentUri uri;
      if (filePath == null) {
        var index = Interlocked.Increment(ref fileIndex);
        filePath = Path.Combine(GetFreshTempPath(), $"testFile{index}.dfy");
      }

      if (filePath.StartsWith("untitled:")) {
        uri = DocumentUri.Parse(filePath);
      } else {
        if (string.IsNullOrEmpty(Path.GetDirectoryName(filePath))) {
          filePath = Path.Combine(GetFreshTempPath(), filePath);
        }
        filePath = Path.GetFullPath(filePath);
        uri = DocumentUri.FromFileSystemPath(filePath);
      }
      return new TextDocumentItem {
        LanguageId = LanguageId,
        Text = source,
        Uri = uri,
        Version = version
      };
    }

    protected static void OpenDocument(ILanguageClient client, TextDocumentItem document) {
      client.DidOpenTextDocument(new DidOpenTextDocumentParams {
        TextDocument = document
      });
    }

    public static string PrintDiagnostics(IEnumerable<Diagnostic> items) {
      return PrintEnumerable(items.Select(PrintDiagnostic));
    }

    public static string PrintDiagnostic(Diagnostic diagnostic) {
      var relatedPrint = string.Join(", ", diagnostic.RelatedInformation?.
        Select(r => $"at {r.Location} saying '{r.Message}'") ?? Array.Empty<string>());
      return $"Diagnostic at {diagnostic.Range} saying '{diagnostic.Message}', related: {relatedPrint}";
    }

    public static string PrintEnumerable(IEnumerable<object> items) {
      return "[" + string.Join(", ", items.Select(o => o.ToString())) + "]";
    }
  }
}