method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
    modifies nums
    ensures 0 <= newLength <= nums.Length
    ensures forall x :: x in nums[..newLength] ==> x != val
    ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
    var i := 0;
    var j := 0;
    
    ghost var oldNums := nums[..];
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant 0 <= j <= i
        invariant forall k :: 0 <= k < j ==> nums[k] != val
        invariant forall k :: j <= k < i ==> nums[k] == oldNums[k]
        invariant multiset(nums[..j]) + multiset(nums[j..i]) == multiset(oldNums[..i])[val := multiset(oldNums[..i])[val] - multiset(nums[..j])[val]]
    {
        if nums[i] != val {
            nums[j] := nums[i];
            j := j + 1;
        }
        i := i + 1;
    }
    newLength := j;
    
    assert forall k :: 0 <= k < newLength ==> nums[k] != val;
    assert forall k :: newLength <= k < nums.Length ==> nums[k] == val;
    assert multiset(nums[..newLength]) + multiset(nums[newLength..]) == multiset(oldNums)[val := 0];
}