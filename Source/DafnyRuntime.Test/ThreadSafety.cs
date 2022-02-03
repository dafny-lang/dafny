using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Coyote;
using Microsoft.Coyote.SystematicTesting;
using Xunit;
using Xunit.Abstractions;

namespace DafnyRuntime.Test {

  public class ThreadSafety {

    ITestOutputHelper Output;

    public ThreadSafety(ITestOutputHelper output) {
      Output = output;
    }

    [Fact(Timeout = 5000)]
    public void RunCoyoteTest() {
      var config = Configuration.Create().WithTestingIterations(500).WithConcurrencyFuzzingEnabled();
      TestingEngine engine = TestingEngine.Create(config, ConcatSequence);
      engine.Run();

      List<string> filenames =
        new List<string>(engine.TryEmitReports(Directory.GetCurrentDirectory(), "ConcatSequence"));
      foreach (var item in filenames) {
        Output.WriteLine("See log file: {0}", item);
      }

      var report = engine.TestReport;
      Assert.True(report.NumOfFoundBugs == 0, $"Coyote found {report.NumOfFoundBugs} bug(s).");
    }

    [Fact]
    public void ReplayCoyoteTest() {
      const string tracePath = "ConcatSequence_0.schedule";
      if (!File.Exists(tracePath)) { return; }
      var trace = File.ReadAllText(tracePath);
      var config = Configuration.Create().WithReplayStrategy(trace);
      TestingEngine engine = TestingEngine.Create(config, ConcatImmutableList);
      engine.Run();

      var report = engine.TestReport;
      Output.WriteLine(report.GetText(config));
      Assert.True(report.NumOfFoundBugs == 0, $"Coyote found {report.NumOfFoundBugs} bug(s).");
    }

    [Test]
    [Fact]
    public static async Task ConcatSequence() {
      //Output.WriteLine("Start Concat");
      var a = Dafny.Sequence<char>.FromString("A");
      var b = Dafny.Sequence<char>.FromString("B");
      var ab = Dafny.Sequence<char>.Concat(a, b);

      var c = Dafny.Sequence<char>.FromString("C");
      var abc = Dafny.Sequence<char>.Concat(ab, c);

      // var elements = helloWorld.Elements;
      var task1 = GetFirstElement(ab);
      var task2 = GetFirstElement(ab);
      var task3 = GetFirstElement(abc);
      var task4 = GetFirstElement(abc);
      var task5 = GetFirstElement(abc);
      var task6 = GetFirstElement(abc);
      var task7 = GetFirstElement(abc);

      var results = await Task.WhenAll(task1, task2, task3, task4, task5, task6, task7);
      var resultStrs = results.Select(arr => new string(arr)).ToArray();

      Assert.Equal("AB", resultStrs[0]);
      Assert.Equal("AB", resultStrs[1]);
      foreach (var result in results.Reverse().Take(5)) {
        Assert.Equal("ABC", new string(result));
      }

      /*Assert.Equal("ABC", resultStrs[2]);
      Assert.Equal("ABC", resultStrs[3]);
      Assert.Equal("ABC", resultStrs[4]);
      Assert.Equal("ABC", resultStrs[5]);
      Assert.Equal("ABC", resultStrs[6]);*/
    }

    private static Task<T[]> GetFirstElement<T>(Dafny.ISequence<T> sequence) {
      return Task.Run(() => sequence.Elements);
    }

    [Fact]
    public async Task ConcatImmutableList() {
      var hello = ImmutableList.CreateRange("Hello ");
      var world = ImmutableList.CreateRange("World!");
      var helloWorld = hello.AddRange(world);
      var task1 = GetFirstElement(helloWorld);
      var task2 = GetFirstElement(helloWorld);
      await Task.WhenAll(task1, task2);
    }

    public Task<T> GetFirstElement<T>(ImmutableList<T> list) {
      return Task.Run(() => { return list[0]; });
    }
  }
}
