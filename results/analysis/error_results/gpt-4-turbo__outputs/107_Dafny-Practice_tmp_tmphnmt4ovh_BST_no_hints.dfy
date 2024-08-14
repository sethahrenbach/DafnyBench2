
datatype Tree = Empty | Node(int, Tree, Tree)

method Main() {
    var tree := BuildBST([-2, 8, 3, 9, 2, -7, 0]);
    PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree) {
    match t {
        case Empty =>
        case Node(n, l, r) =>
            PrintTreeNumbersInorder(l);
            print n;
            print "\n";
            PrintTreeNumbersInorder(r);
    }
}

function NumbersInTree(t: Tree): set<int> {
    NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int> {
    set x | x in q
}

predicate BST(t: Tree) {
    Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int> {
    match t {
        case Empty => []
        case Node(n, left, right) => Inorder(left) + [n] + Inorder(right)
    }
}

predicate Ascending(q: seq<int>) {
    forall i, j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) {
    forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j]
}

method BuildBST(q: seq<int>) returns (t: Tree)
    requires NoDuplicates(q)
    ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
    t := Empty;
    for i := 0 to |q|-1
        invariant BST(t) && NumbersInTree(t) == NumbersInSequence(q[..i])
    {
        t := InsertBST(t, q[i]);
    }
}

method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0) && x !in NumbersInTree(t0)
    ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
{
    match t0 {
        case Empty =>
            t := Node(x, Empty, Empty);
        case Node(i, left, right) =>
            if x < i {
                var tmp := InsertBST(left, x);
                t := Node(i, tmp, right);
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
            } else {
                var tmp := InsertBST(right, x);
                t := Node(i, left, tmp);
                assert NumbersInTree(t) == NumbersInTree(t0) + {x};
            }
    }
    assert BST(t); // Assert to ensure BST property is maintained
}
