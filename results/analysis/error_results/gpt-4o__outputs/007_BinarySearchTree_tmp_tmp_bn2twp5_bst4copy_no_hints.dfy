
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures minValue(tree, res)
{
  match tree {
    case Empty => res := 0; // This case will never be reached due to the precondition
    case Node (Empty, value, _) => res := value;
    case Node (left, _, _) =>
      res := GetMin(left);
  }
}

method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures maxValue(tree, res)
{
  match tree {
    case Empty => res := 0; // This case will never be reached due to the precondition
    case Node (_, value, Empty) => res := value;
    case Node (_, _, right) =>
      res := GetMax(right);
  }
}

method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  res := insertRecursion(tree, value);
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  match tree {
    case Empty => res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if(value == v) {
        res := tree;
      } else if(value < v){
        var temp := insertRecursion(left, value);
        res := Node(temp, v, right);
      } else {
        var temp := insertRecursion(right, value);
        res := Node(left, v, temp);
      }
  }
}

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res)
{
  match tree {
    case Empty => res := tree;
    case Node(left, v, right) =>
      if (value < v){
        var temp := delete(left, value);
        res := Node(temp, v, right);
      } else if (value > v){
        var temp := delete(right, value);
        res := Node(left, v, temp);
      } else {
        if (left == Empty){
          res := right;
        } else if (right == Empty) {
          res := left;
        } else {
          var minVal := GetMin(right);
          var temp := delete(right, minVal);
          res := Node(left, minVal, temp);
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
  //u := delete (u, 1);

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

  // var res := GetMin(u);
  // var max := GetMax(u);
  // print "this is max: ", max;
  //print "this is res: ", res;

  //print u;
}
