using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// The following class stores the relative name of any declaration that is reachable from this module
/// as a list of NameSegments, along with a flag for whether the Declaration is revealed or merely provided.
/// For example, if "A" is a module, a function "A.f()" will be stored in the AccessibleMembers dictionary as
/// the declaration "f" pointing to an AccessibleMember whose AccessPath list contains the NameSegments "A" and "_default".
/// </summary>
public class AccessibleMember(List<NameSegment> accessPath, bool isRevealed = true) {
  public List<NameSegment> AccessPath = accessPath;
  public bool IsRevealed = isRevealed;

  public AccessibleMember(bool isRevealed = true) : this([], isRevealed) {
  }

  public AccessibleMember Clone() {
    return new AccessibleMember(AccessPath.ToList(), IsRevealed);
  }
}