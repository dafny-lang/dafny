namespace Microsoft.Dafny.Compilers;

public class WrapException {

  public static void Throw() {
    throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
  }

}
