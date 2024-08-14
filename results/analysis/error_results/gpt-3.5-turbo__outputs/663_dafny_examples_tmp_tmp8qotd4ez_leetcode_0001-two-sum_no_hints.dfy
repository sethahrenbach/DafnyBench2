predicate InMap(nums: seq<int>, m: map<int, int>, t: int)
  requires nums != null && m != null
  requires forall j :: 0 <= j < |nums| ==> t - nums[j] in m
{
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  requires nums != null
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m := map[int, int]();
  var i := 0;
  while i < nums.Length
    invariant InMap(nums[..i], m, target)
    decreases nums.Length - i
  {
    if nums[i] in m {
      return (m[nums[i]], i);
    }
    m := m + (target - nums[i] := i);
    i := i + 1;
  }
  return (-1, -1);
}