using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

// Same collection as LanguageServerProcessTest: these tests redirect TMPDIR process-wide, and that
// test spawns processes which drop their own temp files, so they must not run concurrently.
[Collection("Sequential Collection")]
public class CoverageTalliesFileTest {

  /// <summary>
  /// The instrumented program writes its branch tallies to a file in the temp directory. That file
  /// used to be left behind on every invocation. Asserting on the shared temp directory would race
  /// with other processes, so this points TMPDIR at a directory of its own -- Path.GetTempPath()
  /// reads the variable on each call rather than caching it -- and requires that nothing remains.
  /// </summary>
  [Fact]
  public async Task ExecutionCoverageLeavesNoTemporaryFile() {
    var sandbox = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    var temp = Path.Combine(sandbox, "temp");
    Directory.CreateDirectory(temp);
    var source = Path.Combine(sandbox, "cov.dfy");
    await File.WriteAllTextAsync(source,
      "method Main() { var i := 0; if i == 0 { print \"a\\n\"; } else { print \"b\\n\"; } }\n");

    var originalTemp = Environment.GetEnvironmentVariable("TMPDIR");
    try {
      Environment.SetEnvironmentVariable("TMPDIR", temp + Path.DirectorySeparatorChar);
      Assert.Equal(temp + Path.DirectorySeparatorChar, Path.GetTempPath());

      var output = new StringWriter();
      var exitCode = await DafnyBackwardsCompatibleCli.MainWithWriters(output, output, TextReader.Null,
        ["run", "--target:cs", "--coverage-report", Path.Combine(sandbox, "report"), source]);
      Assert.Equal(0, exitCode);
      Assert.Contains("a", output.ToString());

      AssertNoTalliesFileRemains(temp);
    }
    finally {
      Environment.SetEnvironmentVariable("TMPDIR", originalTemp);
      try {
        Directory.Delete(sandbox, true);
      } catch (IOException) {
      }
    }
  }

  /// <summary>
  /// A target that does not support execution coverage rejects it, but the instrumenter is
  /// constructed before that check (SinglePassCodeGenerator's constructor), so creating the tallies
  /// file eagerly left one behind on every such invocation with no report to show for it.
  /// </summary>
  [Fact]
  public async Task UnsupportedTargetLeavesNoTemporaryFile() {
    var sandbox = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    var temp = Path.Combine(sandbox, "temp");
    Directory.CreateDirectory(temp);
    var source = Path.Combine(sandbox, "cov.dfy");
    await File.WriteAllTextAsync(source, "method Main() { print \"a\\n\"; }\n");

    var originalTemp = Environment.GetEnvironmentVariable("TMPDIR");
    try {
      Environment.SetEnvironmentVariable("TMPDIR", temp + Path.DirectorySeparatorChar);
      var output = new StringWriter();
      await DafnyBackwardsCompatibleCli.MainWithWriters(output, output, TextReader.Null,
        ["run", "--target:py", "--coverage-report", Path.Combine(sandbox, "report"), source]);
      // The run is expected to fail; what matters is that it cleans up after itself.
      Assert.Contains("not supported", output.ToString());

      AssertNoTalliesFileRemains(temp);
    }
    finally {
      Environment.SetEnvironmentVariable("TMPDIR", originalTemp);
      try {
        Directory.Delete(sandbox, true);
      } catch (IOException) {
      }
    }
  }

  /// <summary>
  /// Asserts that no tallies file remains. TMPDIR is process-wide, so sibling tests running
  /// concurrently drop unrelated files (CLR debug pipes, assemblies they build) into the same
  /// directory; asserting the directory is empty would flake. A tallies file is identified by its
  /// content instead: one unsigned integer per line, one line per instrumented branch.
  /// </summary>
  private static void AssertNoTalliesFileRemains(string temp) {
    foreach (var file in Directory.GetFiles(temp, "tmp*.tmp")) {
      var info = new FileInfo(file);
      // Only ever a few bytes per branch. Guards against reading something that is not a regular
      // file: sibling tests drop FIFOs (CLR debug pipes) here, and reading one blocks forever.
      if (!info.Exists || info.Length > 4096 || info.LinkTarget != null) {
        continue;
      }
      string[] lines;
      try {
        lines = File.ReadAllLines(file);
      } catch (IOException) {
        continue; // still held open by whoever created it, so not ours
      }
      // An empty file counts too: on a target that rejects execution coverage the tallies are
      // never written, so all that is left is the zero-byte file eager creation produced.
      var looksLikeTallies = lines.All(line => uint.TryParse(line, out _));
      Assert.False(looksLikeTallies,
        $"tallies file left behind: {Path.GetFileName(file)}, " +
        (lines.Length == 0 ? "empty" : $"containing {string.Join(",", lines)}"));
    }
  }
}
