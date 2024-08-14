method twoSum(nums: array<int>, target: int) returns (index1: int, index2: int)
    requires 2 <= nums.Length
    requires exists i, j :: (0 <= i < j < nums.Length && nums[i] + nums[j] == target)
    ensures index1 != index2
    ensures 0 <= index1 < nums.Length
    ensures 0 <= index2 < nums.Length
    ensures nums[index1] + nums[index2] == target
{
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
    {
        var j := i + 1;
        while j < nums.Length
            invariant i < j <= nums.Length
            invariant forall l :: i < l < j ==> nums[i] + nums[l] != target
        {
            if nums[i] + nums[j] == target
            {
                index1 := i;
                index2 := j;
                return index1, index2;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}