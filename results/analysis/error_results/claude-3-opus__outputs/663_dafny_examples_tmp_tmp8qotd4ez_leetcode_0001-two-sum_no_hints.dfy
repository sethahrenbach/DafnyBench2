predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

lemma InMapLemma(nums: seq<int>, m: map<int, int>, t: int, i: int)
  requires 0 <= i < |nums|
  requires InMap(nums[..i], m, t)
  ensures t - nums[i] in m
{
  assert InMap(nums[..i], m, t);
  assert |nums[..i]| == i;
  assert 0 <= i < |nums[..i]|;
  assert t - nums[i] in m;
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
    invariant forall j, k :: 0 <= j < k < i ==> nums[j] + nums[k] != target
    invariant InMap(nums[..i], m, target)
  {
    if nums[i] in m {
      var j := m[nums[i]];
      InMapLemma(nums[..i], m, target, j);
      assert 0 <= j < i;
      assert target - nums[j] == nums[i];
      assert nums[j] + nums[i] == target;
      return (j, i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  assert forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target;
  return (-1, -1);
}
