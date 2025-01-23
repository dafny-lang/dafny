// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
using System.CommandLine;
using System.Linq;

namespace Microsoft.Dafny {

  public enum ErrorLevel {
    Info, Warning, Error
  }

  public enum MessageSource {
    Project, Parser, Cloner, RefinementTransformer, Rewriter, Resolver, Translator, Verifier, Compiler, Documentation, TestGeneration
  }

  public record DafnyRelatedInformation(IOrigin Token, string Message);

  public class ErrorReporterSink(DafnyOptions options) : ErrorReporter(options) {
    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
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

  public class ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : BatchErrorReporter(reporter.Options) {
    public readonly ErrorReporter WrappedReporter = reporter;

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
      if (level == ErrorLevel.Warning) {
        return false;
      }

      base.MessageCore(source, level, errorId, tok, msg);
      return WrappedReporter.Message(source, level, errorId, tok, msgPrefix + msg);
    }
  }
}
