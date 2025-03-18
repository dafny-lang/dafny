module FramesExamples {

  import opened Std.Frames

  @AssumeCrossModuleTermination
  trait Tree<T> extends Validatable {
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
      ensures fresh(Repr - left.Repr - right.Repr)
    {
      this.left := left;
      this.value := value;
      this.right := right;

      Repr := {this} + left.Repr + right.Repr;
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

    method RotateRight() 
      requires Valid()
      modifies Repr
      ensures Valid()
    {
      if left is Node<T> {
        var leftAsNode := left as Node<T>;
        var leftValue := leftAsNode.value;
        right := new Node(leftAsNode.right, value, right);
        left := leftAsNode.left;
        value := leftAsNode.value;

        Repr := {this} + left.Repr + right.Repr;
      }
      if (right is Node<T>) {
        assert ValidComponent(right);
        (right as Node<T>).RotateRight();
      }
    }
  }

}