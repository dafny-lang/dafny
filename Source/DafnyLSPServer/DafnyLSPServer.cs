using Microsoft.Boogie;
using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using OmniSharp.Extensions.LanguageServer.Protocol.Server.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Shared;
using OmniSharp.Extensions.LanguageServer.Server;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.IO.Pipelines;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LSPServer
{

  public class DafnyLSPServer
  {
    readonly TextDocumentManager DocumentManager = new TextDocumentManager();
    readonly Dictionary<DocumentUri, List<Diagnostic>> diagnostics = new Dictionary<DocumentUri, List<Diagnostic>>();
    public LanguageServer server;

    static DafnyLSPServer()
    {
      //Dafny.DafnyOptions.Install(new Dafny.DafnyOptions(new DiagnosticErrorReporter()));
    }

    private DafnyLSPServer()
    {

    }

    public static async Task<DafnyLSPServer> Start(PipeReader input, PipeWriter output)
    {
      var result = new DafnyLSPServer();
      result.server = await LanguageServer.From(result.GetServerOptions(input, output));
      return result;
    }

    LanguageServerOptions GetServerOptions(PipeReader input, PipeWriter output)
    {
      var options = new LanguageServerOptions();
      options.WithOutput(output);
      options.WithInput(input);

      var capabilities = new ServerCapabilities();
      RegisterInitializationHandlers(options, capabilities);
      RegisterDocumentHandlers(options, capabilities);

      return options;
    }

    private void RegisterInitializationHandlers(LanguageServerOptions options, ServerCapabilities capabilities)
    {
      options.OnInitialize((server, request, token) =>
      {
        return Task.CompletedTask;
      });
      options.OnInitialized((server, request, response, token) =>
      {
        response.Capabilities = capabilities;
        return Task.CompletedTask;
      });
    }

    private void RegisterDocumentHandlers(LanguageServerOptions options, ServerCapabilities capabilities)
    {
      var registrationOptions = new TextDocumentRegistrationOptions();
      capabilities.TextDocumentSync = new TextDocumentSync(TextDocumentSyncKind.Full);
      options.OnDidOpenTextDocument(didOpenParams => DocumentManager.Open(didOpenParams), registrationOptions);

      var changeRegistrationOptions = new TextDocumentChangeRegistrationOptions();
      options.OnDidChangeTextDocument(didChangeParams =>
      {
        DocumentManager.Change(didChangeParams);
        var errorReporter = new DiagnosticErrorReporter();
        Compile(errorReporter, didChangeParams.TextDocument.Uri);

        if (errorReporter.Diagnostics.Any())
        {
          PublishDiagnosticsParams diagnosticsParams = new PublishDiagnosticsParams();
          diagnosticsParams.Uri = didChangeParams.TextDocument.Uri;

          diagnosticsParams.Diagnostics = errorReporter.Diagnostics.First().Value;
          server.PublishDiagnostics(diagnosticsParams);
        }

      }, changeRegistrationOptions);
      options.OnDidCloseTextDocument(didCloseParams => DocumentManager.Close(didCloseParams), registrationOptions);
    }

    private void PublishDiagnostics(DocumentUri uri)
    {
      PublishDiagnosticsParams diagnosticsParams = new PublishDiagnosticsParams();
      diagnosticsParams.Uri = uri;
      diagnosticsParams.Diagnostics = diagnostics[uri];
      server.PublishDiagnostics(diagnosticsParams);
    }

    void Compile(DiagnosticErrorReporter errorReporter, DocumentUri uri)
    {

      var document = DocumentManager.GetDocument(uri);
      var module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      var builtIns = new BuiltIns();

      var path = uri.GetFileSystemPath();
      var fileName = Path.GetFileName(path);

      var parseCode = Microsoft.Dafny.Parser.Parse(document.Text, fileName, fileName, module, builtIns, errorReporter);
      if (parseCode != 0)
        return;

      var parseIncludesMessage = Main.ParseIncludes(module, builtIns, new List<string>(), new Microsoft.Dafny.Errors(errorReporter));
      if (parseIncludesMessage != null)
        return;

      var dafnyProgram = new Dafny.Program(fileName, module, builtIns, errorReporter);
      var resolver = new Resolver(dafnyProgram);
      resolver.ResolveProgram(dafnyProgram);

      if (errorReporter.Diagnostics.Any())
        return;

      var boogiePrograms = Translator.Translate(dafnyProgram, errorReporter,
          new Translator.TranslatorFlags() { InsertChecksums = true, UniqueIdPrefix = fileName }); // FIXME how are translation errors reported?

      ExecutionEngine.printer = errorReporter.AsBoogieOutputPrinter;
      foreach (var boogieProgram in boogiePrograms) // TODO parallelize?
      {
        BoogieOnce(boogieProgram.Item1, boogieProgram.Item2, errorReporter);
      }

    }

    private bool BoogieOnce(string moduleName, Microsoft.Boogie.Program boogieProgram, DiagnosticErrorReporter errorReporter)
    {
      if (boogieProgram.Resolve() == 0 && boogieProgram.Typecheck() == 0)
      { //FIXME ResolveAndTypecheck?
        ExecutionEngine.EliminateDeadVariables(boogieProgram);
        ExecutionEngine.CollectModSets(boogieProgram);
        ExecutionEngine.CoalesceBlocks(boogieProgram);
        ExecutionEngine.Inline(boogieProgram);

        switch (ExecutionEngine.InferAndVerify(boogieProgram, new PipelineStatistics(), "ServerProgram_" + moduleName, errorReporter.ReportBoogieError,
            DateTime.UtcNow.Ticks.ToString()))
        {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            return true;
        }
      }

      return false;
    }
  }

}
