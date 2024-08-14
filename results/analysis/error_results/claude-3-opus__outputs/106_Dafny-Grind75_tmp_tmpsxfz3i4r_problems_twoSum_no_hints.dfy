/*
https://leetcode.com/problems/two-sum/
function twoSum(nums: number[], target: number): number[] {
    const n = nums.length;
    for(let i = 0; i < n; i++) {
        for(let k = i+1; k < n; k++) {
            if(nums[i] + nums[k] == target) return [i,k]; 
        }
    }
};
*/
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    pair := (0,0);
    var i: nat := 0;
    while i < |nums| 
        invariant i <= |nums|
        invariant forall p: nat, q: nat :: 0 <= p < i && i <= q < |nums| ==> !summingPair(p, q, nums, target)
        invariant exists j: nat :: i <= j < |nums| && summingPair(i, j, nums, target)
    {
        var k: nat := i + 1;
        while k < |nums| 
            invariant i < k <= |nums|
            invariant forall q: nat :: i < q < k ==> !summingPair(i, q, nums, target)
            invariant exists j: nat :: k <= j < |nums| && summingPair(i, j, nums, target)
        {
            if nums[i] + nums[k] == target {
                pair := (i,k);
                return;
            }
            k := k + 1;
        }
        i := i + 1;
    }
}
