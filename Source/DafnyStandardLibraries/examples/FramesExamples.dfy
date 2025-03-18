module FramesExamples {

  import opened Std.Frames

  // A non-trivial example of a recursive data strucutre
  // using the Validatable trait.
  // In particular, expressing the Node class invariant
  // necessary in order to prove termination of recursive methods
  // is much simpler using ValidComponent().

  @AssumeCrossModuleTermination
  trait Tree<T> extends Validatable {

    ghost var nodeCount: nat

    method Elements() returns (result: seq<T>)
      requires Valid()
      decreases Repr
      ensures Valid()
  }

  class Leaf<T> extends Tree<T> {

    constructor () 
      ensures Valid()
    {
      Repr := {this};
      nodeCount := 0;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
    }

    method Elements() returns (result: seq<T>)
      requires Valid()
      decreases Repr
      ensures Valid()
    {
      return [];
    }
  }

  class Node<T> extends Tree<T> {

    var value: T
    var left: Tree<T>
    var right: Tree<T>

    constructor (left: Tree<T>, value: T, right: Tree<T>) 
      requires left.Valid()
      requires right.Valid()
      requires left.Repr !! right.Repr
      ensures Valid()
      ensures this.left == left
      ensures this.value == value
      ensures this.right == right
      ensures fresh(Repr - left.Repr - right.Repr)
    {
      this.left := left;
      this.value := value;
      this.right := right;

      Repr := {this} + left.Repr + right.Repr;
      nodeCount := left.nodeCount + right.nodeCount + 1;
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(left)
      && ValidComponent(right)
      && left.Repr !! right.Repr
      && nodeCount == left.nodeCount + right.nodeCount + 1
    }

    method Elements() returns (result: seq<T>)
      requires Valid()
      decreases Repr
      ensures Valid()
    {
      result := [value];
      var leftElements := left.Elements();
      result := result + leftElements;
      var rightElements := right.Elements();
      result := result + rightElements;
    }

    // Note that Repr CANNOT used as the decreases clause for this method
    // since it allocates new nodes and hence Repr sets grow,
    // even if they contain fresh objects.
    // Instead, it is necessary to define a more domain-specific
    // termination measure based on what work is being done
    // (in this case a count of the number of nodes in subtrees)
    @IsolateAssertions
    method RotateRight() 
      requires Valid()
      modifies Repr
      decreases nodeCount
      ensures ValidAndDisjoint()
    {
      if left is Node<T> {
        var leftAsNode := left as Node<T>;
        
        var leftValue := leftAsNode.value;
        var oldRight := right;
        right := new Node(leftAsNode.right, value, oldRight);
        left := leftAsNode.left;
        value := leftAsNode.value;

        // This kind of "bookkeeping" of ghost state
        // is often necessary.
        // Repeating it at various points in the control flow
        // can look duplicative and noisy,
        // but since it is all ghost state there is no runtime cost,
        // and it often makes verification cheaper and hence less brittle.
        Repr := {this} + left.Repr + right.Repr;
        nodeCount := left.nodeCount + right.nodeCount + 1;
      }

      if (right is Node<T>) {
        (right as Node<T>).RotateRight();

        Repr := {this} + left.Repr + right.Repr;
        nodeCount := left.nodeCount + right.nodeCount + 1;
      }
    }
  }

}