// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
namespace Microsoft.Dafny {

  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration
  }

  public record DafnyRelatedInformation(TokenRange Range, string Message);

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

    public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
      return false;
    }

    public override void Error(MessageSource source, string errorId, IOrigin tok, string msg) {

    }

    public override int Count(ErrorLevel level) {
      return 0;
    }

    public override int CountExceptVerifierAndCompiler(ErrorLevel level) {
      return 0;
    }
  }

  public class ErrorReporterWrapper : BatchErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : base(reporter.Options) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
      if (dafnyDiagnostic.Level == ErrorLevel.Warning) {
        return false;
      }

      base.MessageCore(dafnyDiagnostic);
      return WrappedReporter.MessageCore(dafnyDiagnostic with {
        Message = msgPrefix + dafnyDiagnostic.Message
      });
    }
  }
}
