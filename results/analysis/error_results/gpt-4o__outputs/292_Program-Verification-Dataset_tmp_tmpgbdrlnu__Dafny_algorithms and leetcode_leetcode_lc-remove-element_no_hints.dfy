//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 <= k < i ==> nums[k] != val
    modifies nums
{
    i := 0;
    var end := nums.Length - 1;
    while i <= end 
        invariant 0 <= i <= end + 1 <= nums.Length
        invariant forall k :: 0 <= k < i ==> nums[k] != val
        invariant forall k :: end < k < nums.Length ==> nums[k] == val
    {
        if(nums[i] == val) {
            if(nums[end] == val) {
                end := end - 1;
            } else {
                nums[i], nums[end] := nums[end], nums[i];
                end := end - 1;
            }
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