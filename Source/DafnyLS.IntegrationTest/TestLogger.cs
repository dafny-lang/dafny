using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest {
  /// <summary>
  /// Utility collection to simplify the test implementation.
  /// </summary>
  public static class TestLogger {
    /// <summary>
    /// Creates a logger for the specified type.
    /// </summary>
    /// <typeparam name="TConsumer">The type that uses the logger instance.</typeparam>
    /// <returns>A logger instance.</returns>
    public static ILogger<TConsumer> CreateLogger<TConsumer>() {
      using(var loggerFactory = LoggerFactory.Create(builder => builder.AddConsole().SetMinimumLevel(LogLevel.Debug))) {
        return loggerFactory.CreateLogger<TConsumer>();
      }
    }
  }
}
