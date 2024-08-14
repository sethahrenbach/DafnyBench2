ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  0 <= i < |nums| &&
  0 <= j < |nums| &&
  i != j && // "you may not use the same element twice"
  nums[i] + nums[j] == target
}

method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
{
  var e_to_i := map[int, int];

  for j := 0 to |nums| - 1
    invariant forall k :: 0 <= k < j ==> nums[k] in e_to_i
    invariant forall k :: 0 <= k < j && nums[k] in e_to_i ==> e_to_i[nums[k]] == k
    invariant forall k, l :: 0 <= k < l < j ==> nums[k] + nums[l] != target
  {
    var element := nums[j];
    var rest := target - element;
    if rest in e_to_i {
      var i := e_to_i[rest];
      assert i != j;  // Ensuring different indices
      assert nums[i] + nums[j] == target;  // Ensuring they sum up to target
      return (i, j);
    } else {
      e_to_i := e_to_i[element := j];
    }
  }
  // unreachable here, since there's at least one solution
}