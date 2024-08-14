/* https://leetcode.com/problems/two-sum/
Given an array of integers nums and an integer target, return indices of the two numbers such that they add up to target.
You may assume that each input would have exactly one solution, and you may not use the same element twice.
You can return the answer in any order.

Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].
*/


ghost predicate correct_pair(pair: (int, int), nums: seq<int>, target: int) {
  var (i, j) := pair;
  && 0 <= i < |nums|
  && 0 <= j < |nums|
  && i != j  // "you may not use the same element twice"
  && nums[i] + nums[j] == target
}

// We actually make a weaker pre-condition: there exists at least one solution.
// For verification simplicity, we pretend as if:
// - `seq` were Python list
// - `map` were Python dict
method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  requires exists i, j :: correct_pair((i, j), nums, target)
  ensures correct_pair(pair, nums, target)
{
  // use a map whose keys are elements of `nums`, values are indices,
  // so that we can look up, in constant time, the "complementary partner" for any index.
  var e_to_i := map[];

  // iterate though `nums`, building the map on the fly:
  for j := 0 to |nums|
    invariant forall i' :: 0 <= i' < j && nums[i'] in e_to_i ==> e_to_i[nums[i']] == i'  // (formula A)
    invariant forall i', i'' :: 0 <= i' < j && 0 <= i'' < j && i' != i'' ==> nums[i'] + nums[i''] != target  // (formula B)
    invariant exists i, j :: correct_pair((i, j), nums, target)  // (formula C)
    // the following states the properties of map `e_to_i`:
    // the following says no correct pairs exist among what we've seen so far:
  {
    var element := nums[j];
    var rest := target - element;
    if rest in e_to_i {  // partner found!
      var i := e_to_i[rest];
      assert 0 <= i < j;  // follows from (formula A)
      assert 0 <= j < |nums|;  // follows from loop bounds
      assert i != j;  // follows from (formula B)
      assert nums[i] + element == target;  // follows from `rest in e_to_i` and definition of `rest`
      return (i, j);
    } else {
      e_to_i := e_to_i[element := j];
    }
  }
  assert false;  // unreachable here, since there's at least one solution
}

/* Discussions
1. The error messages indicate that:
   - The invariant (formula A) could not be proved to be maintained by the loop.
   - The expression `e_to_i[nums[i']]` in (formula A) might access an element not in the domain of `e_to_i`.
   - The assertions `0 <= i < j`, `i != j`, and `nums[i] + nums[j] == target` might not hold.

2. The issue with (formula A) is that it assumes `nums[i']` is in `e_to_i` for all `i' < j`, but this is not true when there are duplicate elements in `nums`. We need to weaken the invariant to only consider `i'` where `nums[i']` is actually in `e_to_i`.

3. To fix the domain error in (formula A), we need to add the condition `nums[i'] in e_to_i` before accessing `e_to_i[nums[i']]`.

4. With the updated (formula A), the assertions `0 <= i < j` and `i != j` can be proved:
   - `0 <= i < j` follows from (formula A), because `i` is obtained from `e_to_i[rest]`, and (formula A) ensures that the index stored in `e_to_i` is less than `j`.
   - `i != j` follows from (formula B), because if `i == j`, then `nums[i] + nums[j]` would be equal to `target`, contradicting the invariant.

5. The assertion `nums[i] + element == target` follows from `rest in e_to_i` (implying `nums[i] == rest`) and the definition of `rest`.

6. (formula C) is needed to maintain the precondition that a solution exists throughout the loop iterations, allowing the final `assert false` to be proved.
*/