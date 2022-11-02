using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {

  [TestClass]
  public class NewtonsoftConfiguration {
    private string GetLibraryVersion(string csprojFile, string library) {
      var libraryVersionExtractor = new Regex(
        $"Include=\"{Regex.Escape(library)}\" Version=\"([^\"]+)\"");
      var csprojContent = System.IO.File.ReadAllText(csprojFile);
      var libraryVersion = libraryVersionExtractor.Match(csprojContent);
      Assert.IsTrue(libraryVersion.Success, $"Could not extract {library}'s version from {csprojFile}");
      return libraryVersion.Groups[1].ToString();
    }

    [TestMethod]
    public void NewtonsoftVersionMatch() {
      var dlsNewtonsoftVersion = GetLibraryVersion(@"../../../../DafnyLanguageServer/DafnyLanguageServer.csproj", "Newtonsoft.Json");
      var ddNewtonsoftVersion = GetLibraryVersion(@"../../../../DafnyDriver/DafnyDriver.csproj", "Newtonsoft.Json");
      Assert.AreEqual(dlsNewtonsoftVersion, ddNewtonsoftVersion, "The versions of Newtonsoft.Json in DafnyLanguageServer and DafnyDriver do not match");
    }
  }
}
