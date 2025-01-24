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
}