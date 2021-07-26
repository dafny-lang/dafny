using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using System;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Error reporter implementation that logs the errors to the configured dotnet core logging provider.
  /// </summary>
  public class LogErrorReporter : ErrorReporter {
    private readonly ILogger _logger;

    public LogErrorReporter(ILogger<LogErrorReporter> logger) {
      _logger = logger;
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      var logLevel = ToCoreLogLevel(level);
      if(!_logger.IsEnabled(logLevel)) {
        return false;
      }
      _logger.Log(logLevel, ErrorToString(level, tok, msg));
      return true;
    }

    public override int Count(ErrorLevel level) {
      return 0;
    }

    private static LogLevel ToCoreLogLevel(ErrorLevel level) {
      return level switch {
        ErrorLevel.Error => LogLevel.Error,
        ErrorLevel.Warning => LogLevel.Warning,
        ErrorLevel.Info => LogLevel.Information,
        _ => throw new ArgumentException($"unknown dafny error level {level}")
      };
    }
  }
}
