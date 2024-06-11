using System.Text.RegularExpressions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {

  public class NewtonsoftConfiguration {
    private string GetLibraryVersion(string csprojFile, string library) {
      var libraryVersionExtractor = new Regex(
        $"Include=\"{Regex.Escape(library)}\" Version=\"([^\"]+)\"");
      var csprojContent = System.IO.File.ReadAllText(csprojFile);
      var libraryVersion = libraryVersionExtractor.Match(csprojContent);
      Assert.True(libraryVersion.Success, $"Could not extract {library}'s version from {csprojFile}");
      return libraryVersion.Groups[1].ToString();
    }

    [Fact]
    public void NewtonsoftVersionMatch() {
      var dlsNewtonsoftVersion = GetLibraryVersion(@"../../../../DafnyLanguageServer/DafnyLanguageServer.csproj", "Newtonsoft.Json");
      var ddNewtonsoftVersion = GetLibraryVersion(@"../../../../DafnyDriver/DafnyDriver.csproj", "Newtonsoft.Json");
      Assert.Equal(dlsNewtonsoftVersion, ddNewtonsoftVersion);
    }
  }
}
