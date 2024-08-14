//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 <= k < i ==> nums[k] != val
    ensures forall k :: i <= k < nums.Length ==> nums[k] == val || old(nums[k]) != val
    ensures i <= nums.Length
    modifies nums
{
    i := 0;
    var end := nums.Length - 1;
    while i <= end
        decreases end - i
        invariant 0 <= i <= end + 1 <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[k] != val
        invariant forall k :: end < k < nums.Length ==> nums[k] == val || old(nums[k]) != val
        invariant forall k :: i <= k <= end ==> nums[k] == val || old(nums[k]) != val
    {
        if (nums[i] == val) {
            while nums[end] == val && i < end {
                end := end - 1;
            }
            if i < end {
                nums[i], nums[end] := nums[end], nums[i];
                i := i + 1;
                end := end - 1;
            } else {
                break;
            }
        } else {
            i := i + 1;
        }
    }
}
///compileTarget:js
method Main() {
    var elems := new int[5];
    elems[0] := 1;
    elems[1] := 2;
    elems[2] := 3;
    elems[3] := 4;
    elems[4] := 5;
    var res := removeElement(elems, 5);
    print res, "\n";
    print elems, "\n";
}