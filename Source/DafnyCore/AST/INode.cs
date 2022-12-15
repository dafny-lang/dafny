using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

// public interface INode {
//
//   /// <summary>
//   /// These children should be such that they contain information produced by resolution such as inferred types
//   /// and resolved references. However, they should not be so transformed that source location from the initial
//   /// program is lost. As an example, the pattern matching compilation may deduplicate nodes from the original AST,
//   /// losing source location information, so those transformed nodes should not be returned by this property.
//   /// </summary>
//   IEnumerable<INode> Children { get; }
// }
