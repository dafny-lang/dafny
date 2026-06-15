using Microsoft.Dafny;

namespace DafnyCore.Test;

public class DafnyProjectTest {
  [Fact]
  public void Equality() {
    var randomFileName = Path.GetTempFileName();
    var first = new DafnyProject(null, new Uri(randomFileName, UriKind.Absolute), null,
      new[] { "a", "a2" }.ToHashSet(),
      new[] { "b", "b2" }.ToHashSet(), new Dictionary<string, object>() {
        { "c", "d" },
        { "e", "f" }
      }
    );

    var second = new DafnyProject(null, new Uri(randomFileName, UriKind.Absolute), null,
      new[] { "a2", "a" }.ToHashSet(),
      new[] { "b2", "b" }.ToHashSet(),
      new Dictionary<string, object>() {
        { "e", "f" },
        { "c", "d" },
      }
    );

    Assert.Equal(first, second);

    first.Options.Add("k", "1, 2, 3");
    second.Options.Add("k", "1, 2, 3");

    Assert.Equal(first, second);

    first.Options.Add("m", "1, 2, 3");
    second.Options.Add("m", "3, 2, 1");
    Assert.NotEqual(first, second);
  }

  // Regression test for https://github.com/dafny-lang/dafny/issues/6476: on a case-sensitive OS, an include
  // such as `file.dfy` must not also match `File.dfy`.
  //
  // The strong assertion only applies when this run is on a case-sensitive OS (so the fix is in effect) AND
  // the underlying filesystem actually distinguishes the two files (so the scenario is even constructible).
  // On a typical Linux CI runner both hold, so the regression is genuinely exercised there; on Windows/macOS
  // the test still runs but only checks that ordinary matching keeps working. The OS-keyed approach does not
  // cover atypical volumes (a case-sensitive volume on macOS, or a case-insensitive mount on Linux); those
  // are a known limitation rather than something this test pins down.
  [Fact]
  public void IncludeMatchingDoesNotMatchOtherCasingsOnCaseSensitiveOs() {
    var directory = Path.Combine(Path.GetTempPath(), "dafny-6476-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try {
      File.WriteAllText(Path.Combine(directory, "file.dfy"), "");
      // On a case-insensitive filesystem this overwrites file.dfy (one file remains); on a case-sensitive
      // one it creates a distinct second file.
      File.WriteAllText(Path.Combine(directory, "File.dfy"), "");
      var distinctFilesExist = Directory.GetFiles(directory, "*.dfy").Length == 2;

      var projectUri = new Uri(Path.Combine(directory, DafnyProject.FileName));
      var project = new DafnyProject(null, projectUri, null, new HashSet<string> { "file.dfy" });

      var matched = project.GetRootSourceUris(OnDiskFileSystem.Instance)
        .Select(uri => Path.GetFileName(uri.LocalPath)).ToHashSet();

      var caseSensitiveOs = DafnyProject.FileSystemCaseComparison == StringComparison.Ordinal;
      if (caseSensitiveOs && distinctFilesExist) {
        // The include `file.dfy` selects only `file.dfy`, never the unrelated `File.dfy`.
        Assert.Contains("file.dfy", matched);
        Assert.DoesNotContain("File.dfy", matched);
      } else {
        // Case-insensitive OS/filesystem: the include still resolves the (single) file.
        Assert.NotEmpty(matched);
      }
    } finally {
      Directory.Delete(directory, true);
    }
  }
}
