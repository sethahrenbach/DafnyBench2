// If this invariant is added explicitly to the loop then the verification never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
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
    invariant forall k :: 0 <= k < i ==> target - nums[k] in m
    invariant forall k :: 0 <= k < i ==> m[target - nums[k]] == k
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> nums[k1] + nums[k2] != target
  {
    if nums[i] in m {
      assert 0 <= m[nums[i]] < i;
      assert nums[m[nums[i]]] + nums[i] == target;
      return (m[nums[i]], i);
    }
    m := m[target - nums[i] := i];
    assert forall k :: 0 <= k < i + 1 ==> target - nums[k] in m;
    assert forall k :: 0 <= k < i + 1 ==> m[target - nums[k]] == k;
    i := i + 1;
  }
  assert forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target;
  return (-1, -1);
}