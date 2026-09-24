#nullable enable
using System;
using System.Diagnostics;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

public interface IPerformanceLogger {
  void TrackTime(string activity, string[] arguments, long millis);

  async Task<T> TrackAsync<T>(string activity, string[] arguments, Func<Task<T>> getTask) {
    Stopwatch sw = Stopwatch.StartNew();
    var result = await getTask();
    TrackTime(activity, arguments, sw.ElapsedMilliseconds);
    return result;
  }
  
  async Task TrackAsync(string activity, string[] arguments, Func<Task> getTask) {
    Stopwatch sw = Stopwatch.StartNew();
    await getTask();
    TrackTime(activity, arguments, sw.ElapsedMilliseconds);
  }
  
  T Track<T>(string activity, string[] arguments, Func<T> doActivity) {
    Stopwatch sw = Stopwatch.StartNew();
    var result = doActivity();
    TrackTime(activity, arguments, sw.ElapsedMilliseconds);
    return result;
  }
}

public class VoidPerformanceLogger : IPerformanceLogger {
  public void TrackTime(string activity, string[] arguments, long millis) {
  }
}

public class PerformanceLogger(IDafnyOutputWriter outputWriter) : IPerformanceLogger {
  public void TrackTime(string activity, string[] arguments, long millis) {
    _ = outputWriter.Status($"Time to do {activity} was {millis}ms");
  }
}