
method removeElement(nums: array<int>, val: int) returns (i: int)
    requires nums != null
    requires nums.Length > 0
    ensures forall k :: 0 <= k < i < nums.Length ==> nums[k] != val
    modifies nums
{
    var idx := 0;
    var end := nums.Length - 1;
    while idx <= end 
        invariant 0 <= idx <= nums.Length
        invariant 0 <= end < nums.Length
        invariant forall k :: 0 <= k < idx < nums.Length ==> nums[k] != val
    {
        if(nums[idx] == val) {
            if(nums[end] == val) {
                end := end - 1;
            }else{
                nums[idx], nums[end] := nums[end], nums[idx];
                idx := idx + 1;
                end := end - 1;
            }
        }else{
            idx := idx + 1;
        }
    }
}

///compileTarget:js
method Main() {
    var elems := new int[5][1,2,3,4,5];
    var res := removeElement(elems, 5);
    print res, "\n", elems;
}
