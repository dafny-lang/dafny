using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
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
using System.IO.Pipelines;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest {
  public class DafnyLanguageServerTestBase : LanguageServerTestBase {
    protected const string SlowToVerify = @"
lemma {:timeLimit 10} SquareRoot2NotRational(p: nat, q: nat)
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
}";

    public const string LanguageId = "dafny";
    protected static int fileIndex;

    public ILanguageServer Server { get; private set; }

    public IDocumentDatabase Documents => Server.GetRequiredService<IDocumentDatabase>();

    public DafnyLanguageServerTestBase() : base(new JsonRpcTestOptions(LoggerFactory.Create(builder => builder.AddConsole().SetMinimumLevel(LogLevel.Warning)))) { }

    protected override (Stream clientOutput, Stream serverInput) SetupServer() {
      var clientPipe = new Pipe(TestOptions.DefaultPipeOptions);
      var serverPipe = new Pipe(TestOptions.DefaultPipeOptions);
      Server = OmniSharp.Extensions.LanguageServer.Server.LanguageServer.PreInit(
        options => options
          .WithInput(serverPipe.Reader)
          .WithOutput(clientPipe.Writer)
          .ConfigureLogging(SetupTestLogging)
          .WithDafnyLanguageServer(CreateConfiguration(), () => { })
      );
      // This is the style used in the LSP implementation itself:
      // https://github.com/OmniSharp/csharp-language-server-protocol/blob/1b6788df2600083c28811913a221ccac7b1d72c9/test/Lsp.Tests/Testing/LanguageServerTestBaseTests.cs
#pragma warning disable VSTHRD110 // Observe result of async calls
      Server.Initialize(CancellationToken);
#pragma warning restore VSTHRD110 // Observe result of async calls
      return (clientPipe.Reader.AsStream(), serverPipe.Writer.AsStream());
    }

    protected virtual IConfiguration CreateConfiguration() {
      return new ConfigurationBuilder().Build();
    }

    private static void SetupTestLogging(ILoggingBuilder builder) {
      builder
        .AddConsole()
        .SetMinimumLevel(LogLevel.Debug)
        .AddFilter("OmniSharp", LogLevel.Warning);
    }

    protected static TextDocumentItem CreateTestDocument(string source, string filePath = null, int version = 1) {
      filePath ??= $"testFile{fileIndex++}.dfy";
      return new TextDocumentItem {
        LanguageId = LanguageId,
        Text = source,
        Uri = DocumentUri.FromFileSystemPath(filePath),
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
