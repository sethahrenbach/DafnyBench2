
function hasPathSum(root: TreeNode, targetSum: int): bool
    ensures exists p: seq<TreeNode> | isPath(p, root) && pathSum(p) == targetSum
{
    if root == Nil {
        return false;
    }

    if(root.val - targetSum == 0 && root.left == Nil && root.right == Nil) {
        return true;
    }
    var leftPath := hasPathSum(root.left, targetSum-root.val);
    var rightPath := hasPathSum(root.right, targetSum-root.val);

    if leftPath {
        ghost var p: seq<TreeNode> :| isPath(p, root.left) && pathSum(p) == targetSum-root.val;
    }
    if rightPath {
        ghost var p: seq<TreeNode> :| isPath(p, root.right) && pathSum(p) == targetSum-root.val;
    }
    return leftPath || rightPath;
}
