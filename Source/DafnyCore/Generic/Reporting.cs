// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable
using System;
using System.Collections.Generic;
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
  public record DafnyDiagnostic(MessageSource Source, string ErrorId, IOrigin Token, string Message, ErrorLevel Level,
    IReadOnlyList<DafnyRelatedInformation> RelatedInformation) : IComparable<DafnyDiagnostic> {
    public int CompareTo(DafnyDiagnostic? other) {
      if (other == null) {
        return 1;
      }
      var r0 = Token.Center.CompareTo(other.Token.Center);
      if (r0 != 0) {
        return r0;
      }

      for (var index = 0; index < RelatedInformation.Count; index++) {
        if (other.RelatedInformation.Count > index) {
          var r1 = RelatedInformation[index].Token.Center.CompareTo(other.RelatedInformation[index].Token.Center);
          if (r1 != 0) {
            return r1;
          }
        } else {
          return 1;
        }
      }

      if (other.RelatedInformation.Count > RelatedInformation.Count) {
        return -1;
      }

      return 0;
    }
  }

  public class ErrorReporterSink : ErrorReporter {
    public ErrorReporterSink(DafnyOptions options) : base(options) { }

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

  public class ErrorReporterWrapper : BatchErrorReporter {

    private string msgPrefix;
    public readonly ErrorReporter WrappedReporter;

    public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : base(reporter.Options) {
      this.msgPrefix = msgPrefix;
      this.WrappedReporter = reporter;
    }

    protected override bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
      if (level == ErrorLevel.Warning) {
        return false;
      }

      base.MessageCore(source, level, errorId, tok, msg);
      return WrappedReporter.Message(source, level, errorId, tok, msgPrefix + msg);
    }
  }
}
