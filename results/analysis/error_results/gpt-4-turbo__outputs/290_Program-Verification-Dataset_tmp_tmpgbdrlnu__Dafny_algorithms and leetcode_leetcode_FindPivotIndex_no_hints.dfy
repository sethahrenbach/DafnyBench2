
function sum(nums: seq<int>): int
  decreases nums
{
  if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)]) + nums[|nums|-1]
}

method FindPivotIndex(nums: seq<int>) returns (index: int)
  requires |nums| > 0
  ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
  ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
  var totalSum := sum(nums);
  var leftSum := 0;
  var rightSum := totalSum;

  for i: nat := 0 to |nums|
    invariant 0 <= i <= |nums|
    invariant leftSum == sum(nums[0..i])
    invariant rightSum == sum(nums[i..])
    invariant forall j: nat | 0 <= j < i :: sum(nums[0..j]) != sum(nums[(j+1)..])
  {
    if leftSum == rightSum {
      return i;
    }
    if i < |nums| {
      leftSum := leftSum + nums[i];
      rightSum := rightSum - nums[i];
    }
  }
  return -1;
}
