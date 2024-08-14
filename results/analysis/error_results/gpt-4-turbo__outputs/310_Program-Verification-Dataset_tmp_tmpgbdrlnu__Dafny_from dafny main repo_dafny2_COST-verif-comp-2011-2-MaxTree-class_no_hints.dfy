class Tree {
  var value: int;
  var left: Tree?;
  var right: Tree?;

  ghost var Contents: seq<int>;
  ghost var Repr: set<object>;

  predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    ((left == this && right == this && Contents == []) ||
     (left != this && right != this && left in Repr && left.Repr <= Repr && this !in left.Repr &&
      right in Repr && right.Repr <= Repr && this !in right.Repr &&
      left.Valid() && right.Valid() &&
      Contents == left.Contents + [value] + right.Contents))
  }

  function IsEmpty(): bool
    requires Valid()
    reads this, Repr
  {
    left == this && right == this
  }

  constructor Empty()
    ensures Valid() && Contents == []
  {
    left, right := this, this;
    Repr := {this};
    Contents := [];
  }

  constructor Node(lft: Tree, val: int, rgt: Tree)
    requires lft.Valid() && rgt.Valid()
    ensures Valid() && Contents == lft.Contents + [val] + rgt.Contents
  {
    left, value, right := lft, val, rgt;
    Repr := {this} + lft.Repr + rgt.Repr;
    Contents := lft.Contents + [val] + rgt.Contents;
  }

  method ComputeMax() returns (mx: int)
    requires Valid() && !IsEmpty()
    ensures forall x :: x in Contents ==> x <= mx
    ensures exists x :: x in Contents && x == mx
  {
    mx := value;
    if (!left.IsEmpty()) {
      var m := left.ComputeMax();
      mx := if mx < m then m else mx;
    }
    if (!right.IsEmpty()) {
      var m := right.ComputeMax();
      mx := if mx < m then m else mx;
    }
  }
}