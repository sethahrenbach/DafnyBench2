
method twoSum(nums: array<int>, target: int) returns (i: int, j: int)
  requires nums.Length > 1
  requires exists i,j::0 <= i < j < nums.Length &&  nums[i] + nums[j] == target
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
  ensures forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
{
  var n := nums.Length;
  i := 0;
  j := 1;
  while i < n - 1
    invariant 0 <= i < n
    invariant 1 <= j <= n
    invariant i < j <= n
    invariant forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
    invariant forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
  {
    j := i + 1;
    while j < n
      invariant 0 <= i < n
      invariant 1 <= j <= n
      invariant i < j <= n
      invariant forall ii,jj:: (0 <= ii < i && ii < jj < nums.Length)  ==> nums[ii] + nums[jj] != target
      invariant forall jj:: i < jj < j ==> nums[i] + nums[jj] != target
    {
      assert 0 <= i < j < nums.Length;
      assert nums[i] + nums[j] != target;
      j := j + 1;
    }

    i := i + 1;
  }
}
