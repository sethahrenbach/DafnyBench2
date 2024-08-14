datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)

function TreeSeq(root: TreeNode): seq<TreeNode> {
    match root {
        case Nil => []
        case Cons(val, left, right) => [root] + TreeSeq(left) + TreeSeq(right)
    }
}

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
    if |paths| == 0 then false 
    else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => 
            if |paths| == 1 then root == paths[0] && root.left == Nil && root.right == Nil
            else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}

function pathSum(paths: seq<TreeNode>): nat {
    if |paths| == 0 then 0 
    else match paths[0] {
        case Nil => 0
        case Cons(val, left, right) => val + pathSum(paths[1..])
    }
}

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
    if root == Nil {
        return false;
    }

    if(root.val == targetSum && root.left == Nil && root.right == Nil) {
        return true;
    }

    var leftPath := hasPathSum(root.left, targetSum - root.val);
    var rightPath := hasPathSum(root.right, targetSum - root.val);

    if leftPath {
        ghost var p := [root] + TreeSeq(root.left);
        assert isPath(p, root) && pathSum(p) == targetSum;
        return true;
    }
    if rightPath {
        ghost var p := [root] + TreeSeq(root.right);
        assert isPath(p, root) && pathSum(p) == targetSum;
        return true;
    }

    return false;
}

method Test() {
    var c := Cons(3, Nil, Nil);
    var b := Cons(2, c, Nil);
    var a := Cons(1, b, Nil);
}