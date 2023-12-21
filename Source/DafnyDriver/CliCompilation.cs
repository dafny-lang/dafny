using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

public class CliCompilation {
  private readonly DafnyOptions options;
  
  private readonly CreateCompilation createCompilation;

  public static Compilation Create(DafnyOptions options) {
    var me = new CliCompilation(options);
    return me.Create();
  }
  
  public CliCompilation(DafnyOptions options) {
    this.options = options;

    var fileSystem = OnDiskFileSystem.Instance;
    ILoggerFactory factory = new LoggerFactory();
    var telemetryPublisher = new TelemetryPublisher(factory.CreateLogger<ITelemetryPublisher>());
    createCompilation = (engine, input) => new Compilation(factory.CreateLogger<Compilation>(), fileSystem,
      new TextDocumentLoader(factory.CreateLogger<ITextDocumentLoader>(),
        new DafnyLangParser(this.options, fileSystem, telemetryPublisher,
          factory.CreateLogger<DafnyLangParser>(),
          factory.CreateLogger<CachingParser>()),
        new DafnyLangSymbolResolver(factory.CreateLogger<DafnyLangSymbolResolver>(),
          factory.CreateLogger<CachingResolver>(),
          telemetryPublisher)), new DafnyProgramVerifier(factory.CreateLogger<DafnyProgramVerifier>()),
      engine, input);
  }

  private Compilation Create() {
    var me = new CliCompilation(options);
    if (options.DafnyProject == null) {
      var uri = options.CliRootSourceUris.First();
      options.DafnyProject = new DafnyProject {
        Includes = Array.Empty<string>(),
        Uri = uri
      };
    }

    options.RunningBoogieFromCommandLine = true;

    var input = new CompilationInput(options, 0, options.DafnyProject);
    var executionEngine = new ExecutionEngine(options, new VerificationResultCache(), DafnyMain.LargeThreadScheduler);
    var compilation = createCompilation(executionEngine, input);
    
    ErrorReporter consoleReporter = options.DiagnosticsFormat switch {
      DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
      DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
      _ => throw new ArgumentOutOfRangeException()
    };

    compilation.Updates.Subscribe(ev => {
      if (ev is NewDiagnostic newDiagnostic) {
        var dafnyDiagnostic = newDiagnostic.Diagnostic;
        consoleReporter.Message(dafnyDiagnostic.Source, dafnyDiagnostic.Level,
          dafnyDiagnostic.ErrorId, dafnyDiagnostic.Token, dafnyDiagnostic.Message);
      } else if (ev is FinishedResolution finishedResolution) {
        DafnyMain.MaybePrintProgram(finishedResolution.ResolvedProgram, options.DafnyPrintResolvedFile, true);

        if (finishedResolution.ResolvedProgram.Reporter.ErrorCountUntilResolver != 0) {
          var message = string.Format("{0} resolution/type errors detected in {1}", finishedResolution.ResolvedProgram.Reporter.Count(ErrorLevel.Error),
            finishedResolution.ResolvedProgram.Name);
          options.OutputWriter.WriteLine(message);
        }
      }
      
    });
    return compilation;
  }
}

class TelemetryPublisher : ITelemetryPublisher {
  private readonly ILogger<ITelemetryPublisher> logger;

  public TelemetryPublisher(ILogger<ITelemetryPublisher> logger) {
    this.logger = logger;
  }

  public void PublishTelemetry(ImmutableDictionary<string, object> data) {
    // TODO throw new NotImplementedException();
  }

  // TODO make ITelemetryPublisher abstract class and move this there.
  public void PublishUnhandledException(Exception e) {
    logger.LogError(e, "exception occurred");
    PublishTelemetry(ImmutableDictionary.Create<string, object>().
      Add("kind", ITelemetryPublisher.TelemetryEventKind.UnhandledException).
      Add("payload", e.ToString()));
  }
}