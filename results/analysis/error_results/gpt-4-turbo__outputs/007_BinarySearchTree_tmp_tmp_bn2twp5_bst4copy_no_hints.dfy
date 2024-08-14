
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
{
  match tree
  case Empty => true
  case Node(left, value, right) =>
    (left == Empty || (left.value < value && maxValue(left, value)))
    && (right == Empty || (right.value > value && minValue(right, value)))
    && BinarySearchTree(left) && BinarySearchTree(right)
}

predicate maxValue(tree: Tree, max: int)
{
  match tree
  case Empty => true
  case Node(left, v, right) => v < max && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
{
  match tree
  case Empty => true
  case Node(left, v, right) => v > min && minValue(left, min) && minValue(right, min)
}

method GetMin(tree: Tree) returns (res: int)
  requires BinarySearchTree(tree) && tree != Empty
  ensures BinarySearchTree(tree) && minValue(tree, res)
{
  match tree {
    case Empty => res := 0; // This case will never occur due to precondition
    case Node(Empty, value, _) => res := value;
    case Node(left, _, _) => res := GetMin(left);
  }
}

method GetMax(tree: Tree) returns (res: int)
  requires BinarySearchTree(tree) && tree != Empty
  ensures BinarySearchTree(tree) && maxValue(tree, res)
{
  match tree {
    case Empty => res := 0; // This case will never occur due to precondition
    case Node(_, value, Empty) => res := value;
    case Node(_, _, right) => res := GetMax(right);
  }
}

method insert(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  res := insertRecursion(tree, value);
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  match tree {
    case Empty => res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if (value < v) {
        var newLeft := insertRecursion(left, value);
        res := Node(newLeft, v, right);
        assert BinarySearchTree(res);
      } else if (value > v) {
        var newRight := insertRecursion(right, value);
        res := Node(left, v, newRight);
        assert BinarySearchTree(res);
      } else {
        res := tree;
      }
  }
}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  match tree {
    case Empty => res := Empty;
    case Node(left, v, right) =>
      if (value < v) {
        var newLeft := delete(left, value);
        res := Node(newLeft, v, right);
        assert BinarySearchTree(res);
      } else if (value > v) {
        var newRight := delete(right, value);
        res := Node(left, v, newRight);
        assert BinarySearchTree(res);
      } else {
        if (left == Empty) {
          res := right;
        } else if (right == Empty) {
          res := left;
        } else {
          var minRight := GetMin(right);
          var newRight := delete(right, minRight);
          res := Node(left, minRight, newRight);
          assert BinarySearchTree(res);
        }
      }
  }
}

method Inorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Inorder(left);
      print value, ", ";
      Inorder(right);
  }
}

method Postorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Postorder(left);
      Postorder(right);
      print value, ", ";
  }
}

method Main() {
  var tree := insert(Empty, 3);
  var u := insert(tree, 2);

  u := insert(u, 7);
  u := insert(u, 6);
  u := insert(u, 9);

  print "This is Inorder: ";
  Inorder(u);
  print "\n";

  print "This is Postorder: ";
  Postorder(u);
  print "\n";

  print "tree before delete: ", u, "\n";

  u := delete(u, 7);
  print "tree after delete: ", u, "\n";

  print "This is Inorder: ";
  Inorder(u);

  print "\n";
  print "This is Postorder: ";
  Postorder(u);
}
