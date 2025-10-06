namespace Microsoft.Dafny;

public class ExprHeapUsage {
  public bool UseHeap = false;
  public bool UseReferrersHeap = false;
  public bool UseOldHeap = false;

  public static ExprHeapUsage DontCare = new ExprHeapUsage();
}