using System;
using System.Security.Cryptography;
using System.Threading.Tasks;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Running;

namespace MyBenchmarks
{
    public class SequenceRace
    {
        private readonly Dafny.ISequence<int> s;
        

        public SequenceRace() {
          s = Dafny.Sequence<int>.FromArray(Array.Empty<int>());
          for (var i = 0; i <= 1000; i++) {
            s = Dafny.Sequence<int>.Concat(s, Dafny.Sequence<int>.FromArray(new int[]{ i }));
          }
        }

        [Benchmark]
        public void LazyRaceParallel() {
          Parallel.For(0, 10, _ => {
            LazyRace();
          });
        }
        
        private void LazyRace() {
          s.Select(0);
        }
    }

    public class Program
    {
        public static void Main(string[] args)
        {
            var summary = BenchmarkRunner.Run<SequenceRace>(
              DefaultConfig.Instance.AddJob(
                Job.Default.WithAffinity((IntPtr)(2 ^ Environment.ProcessorCount - 1))
                  .WithIterationTime()));
        }
    }
}