module FramesExamples {

  import opened Std.Frames
  import opened Std.Wrappers

  // A non-trivial example of a recursive data strucutre
  // using the Validatable trait.
  // In particular, expressing the Node class invariant
  // necessary in order to prove termination of recursive methods
  // is much simpler using ValidComponent().

  @AssumeCrossModuleTermination
  trait Tree<T> extends Validatable {

    ghost var nodeCount: nat

    function Elements(): seq<T>
      requires Valid()
      reads this, Repr
      decreases Repr
      ensures Valid()
  }

  class Leaf<T> extends Tree<T> {

    constructor ()
      reads {}
      ensures Valid()
      ensures fresh(Repr)
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

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    function Elements(): seq<T>
      requires Valid()
      reads this, Repr
      decreases Repr
      ensures Valid()
    {
      []
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
      reads left, left.Repr, right, right.Repr
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

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    function Elements(): seq<T>
      requires Valid()
      reads this, Repr
      decreases Repr
      ensures Valid()
    {
      [value] + left.Elements() + right.Elements()
    }

    // Note that Repr CANNOT used as the decreases clause for this method
    // since it allocates new nodes and hence Repr sets grow,
    // even if they contain fresh objects.
    // Instead, it is necessary to define a more domain-specific
    // termination measure based on what work is being done
    // (in this case a count of the number of nodes in subtrees)
    @IsolateAssertions
    @ResourceLimit("1e7")
    method RotateRight()
      requires Valid()
      modifies Repr
      decreases nodeCount
      ensures ValidChange()
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

      if right is Node<T> {
        (right as Node<T>).RotateRight();

        Repr := {this} + left.Repr + right.Repr;
        nodeCount := left.nodeCount + right.nodeCount + 1;
      }
    }
  }

}