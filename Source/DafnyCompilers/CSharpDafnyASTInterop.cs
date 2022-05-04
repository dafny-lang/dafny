namespace CSharpDafnyASTInterop {
  public partial class TypeUtils {
    public static Microsoft.Dafny.Type NormalizeExpand(Microsoft.Dafny.Type ty) =>
      ty.NormalizeExpand();
  }
}
