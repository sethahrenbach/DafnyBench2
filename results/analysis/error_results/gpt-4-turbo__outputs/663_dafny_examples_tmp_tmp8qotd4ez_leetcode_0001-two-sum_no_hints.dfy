predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && 
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall k :: 0 <= k < i ==> (target - nums[k]) in m
    invariant forall k, l :: 0 <= k < l < i ==> nums[k] + nums[l] != target
    invariant forall k :: 0 <= k < i ==> m[target - nums[k]] == k
  {
    if nums[i] in m {
      assert 0 <= m[nums[i]] < i; // Ensure m[nums[i]] is a valid index and less than i
      assert nums[m[nums[i]]] + nums[i] == target; // Ensure the sum is indeed the target
      return (m[nums[i]], i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  return (-1, -1);
}