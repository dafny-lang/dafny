using System.Globalization;
using System.Threading;
using Microsoft.Dafny;
using Xunit;

namespace DafnyCore.Test;

public class CounterExampleCultureTest {

  /// <summary>
  /// Boogie's model parser used the ambient culture to recognize numeric literals, so under a
  /// locale whose decimal separator is a comma it rejected reals such as "0.0" and no
  /// counterexample could be produced (https://github.com/dafny-lang/dafny/issues/6475).
  /// The parser lives in Boogie, so this pins the behavior the dependency bump fixes.
  ///
  /// The culture is set on a thread this test owns rather than on the calling thread. It has to be
  /// set somewhere -- Model.ParseModels takes no IFormatProvider -- but xunit runs test classes in
  /// parallel on pool threads it reuses, so mutating the caller's culture could be observed by a
  /// concurrently running test. Restoring in a finally would not help: the window is while this
  /// test runs, not after it.
  /// </summary>
  [Fact]
  public void ExtractModelParsesRealsUnderCommaDecimalLocale() {
    object model = null;
    System.Exception failure = null;
    var thread = new Thread(() => {
      CultureInfo.CurrentCulture = new CultureInfo("fr-FR");
      try {
        model = DafnyModel.ExtractModel(DafnyOptions.Default,
          "*** MODEL\nx -> 0.0\n*** END_MODEL\n");
      } catch (System.Exception e) {
        // Must be caught here: an exception escaping a manually started thread takes down the
        // whole test host instead of failing this test, which is how the pre-bump behavior shows up.
        failure = e;
      }
    });
    thread.Start();
    Assert.True(thread.Join(60_000), "the model parse did not finish");
    Assert.Null(failure);
    Assert.NotNull(model);
  }
}
