using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny; 

public class InternalDocstringRewritersPluginConfiguration : Plugins.PluginConfiguration {
  public static readonly InternalDocstringRewritersPluginConfiguration Singleton = new();
  public static readonly Plugin Plugin = new ConfiguredPlugin(Singleton);

  public override DocstringRewriter[] GetDocstringRewriters(DafnyOptions options) {
    if (options.UseJavadocLikeDocstringRewriter) {
      return new DocstringRewriter[] {
        new JavadocLikeDocstringRewriter()
      };
    } else {
      return new DocstringRewriter[] { };
    }
  }
}