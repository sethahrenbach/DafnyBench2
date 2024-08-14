//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 <= k < i ==> nums[k] != val
    ensures forall k :: i <= k < nums.Length ==> nums[k] == old(nums[k])
    modifies nums
{
    i := 0;
    var n := nums.Length;
    var end := n - 1;
    
    while i <= end
        invariant 0 <= i <= end + 1 <= n
        invariant forall k :: 0 <= k < i ==> nums[k] != val
        invariant forall k :: i <= k <= end ==> nums[k] == old(nums[k]) || (exists j :: i <= j <= n-1 && nums[k] == old(nums[j])) || nums[k] == val
        invariant forall k :: end < k < n ==> nums[k] == old(nums[k])
    {
        if nums[i] == val {
            nums[i] := nums[end];
            end := end - 1;
        } else {
            i := i + 1;
        }
    }
}

///compileTarget:js
method Main() {
    var elems := new int[5][1,2,3,4,5];
    var res := removeElement(elems, 5);
    print res, "\n", elems;
}
