using Microsoft.Dafny;

namespace DafnyCore.Test; 

public class DafnyProjectTest {
  [Fact]
  public void Equality() {
    var randomFileName = Path.GetTempFileName();
    var first = new DafnyProject() {
      Uri = new Uri(randomFileName, UriKind.Absolute),
      Includes = new[] { "a", "a2" },
      Excludes = new[] { "b", "b2" },
      Options = new Dictionary<string, object>() {
        { "c", "d" },
        { "e", "f" }
      }
    };

    var second = new DafnyProject() {
      Uri = new Uri(randomFileName, UriKind.Absolute),
      Includes = new[] { "a2", "a" },
      Excludes = new[] { "b2", "b" },
      Options = new Dictionary<string, object>() {
        { "e", "f" },
        { "c", "d" },
      }
    };

    Assert.Equal(first, second);

    first.Options.Add("k", new[] { 1, 2, 3 });
    second.Options.Add("k", new[] { 1, 2, 3 });

    Assert.Equal(first, second);

    first.Options.Add("m", new[] { 1, 2, 3 });
    second.Options.Add("m", new[] { 3, 2, 1 });
    Assert.NotEqual(first, second);
  }
}