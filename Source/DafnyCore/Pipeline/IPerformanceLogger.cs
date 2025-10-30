#nullable enable
using System;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

public interface IPerformanceLogger {
  void TrackTime(string activity, string[] arguments, TimeSpan span);

  async Task<T> TrackAsync<T>(string activity, string[] arguments, Func<Task<T>> getTask) {
    var before = DateTime.Now;
    var result = await getTask();
    TrackTime(activity, arguments, DateTime.Now - before);
    return result;
  }
  
  async Task TrackAsync(string activity, string[] arguments, Func<Task> getTask) {
    var before = DateTime.Now;
    await getTask();
    TrackTime(activity, arguments, DateTime.Now - before);
  }
  
  T Track<T>(string activity, string[] arguments, Func<T> doActivity) {
    var before = DateTime.Now;
    var result = doActivity();
    TrackTime(activity, arguments, DateTime.Now - before);
    return result;
  }
}

public class VoidPerformanceLogger : IPerformanceLogger {
  public void TrackTime(string activity, string[] arguments, TimeSpan span) {
  }
}

public class PerformanceLogger(IDafnyOutputWriter outputWriter) : IPerformanceLogger {
  public record Entry(string Activity, string[] Arguments, TimeSpan Span);

  public void TrackTime(string activity, string[] arguments, TimeSpan span) {
    _ = outputWriter.Status($"Time to do {activity} was {span.Milliseconds}ms");
  }
}