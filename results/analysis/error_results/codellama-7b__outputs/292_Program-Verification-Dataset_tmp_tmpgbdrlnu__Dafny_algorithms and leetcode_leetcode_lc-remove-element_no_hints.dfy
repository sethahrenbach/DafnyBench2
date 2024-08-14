
method removeElement(nums: array<int>, val: int) returns (i: int)
    ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
    modifies nums
    loop invariant 0 <= i <= nums.Length
    loop invariant forall k :: 0 <= k < i ==> nums[k] != val
    loop invariant forall k :: i <= k < nums.Length ==> nums[k] != val
    loop assigns nums[0..nums.Length-1]
{
    i := 0;
    var end := nums.Length - 1;
    while i < end 
    {
        if(nums[i] == val) {
            if(nums[end] == val) {
                end := end - 1;
            }else{
                nums[i], nums[end] := nums[end], nums[i];
                i := i + 1;
                end := end  - 1;
            }
        }else{
            i := i + 1;
        }
    }
}
