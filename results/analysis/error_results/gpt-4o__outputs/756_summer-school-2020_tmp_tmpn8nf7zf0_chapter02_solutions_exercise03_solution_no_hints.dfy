predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  IsSorted(output) && multiset(output) == multiset(input)
}

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := merge_sort(left);
    var rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    assert multiset(output) == multiset(leftSorted) + multiset(rightSorted);
    assert multiset(leftSorted) == multiset(left);
    assert multiset(rightSorted) == multiset(right);
    assert multiset(left + right) == multiset(input);
    assert multiset(output) == multiset(input);
  }
}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(output)
  ensures SortSpec(a+b, output)
  decreases |a|+|b|
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant IsSorted(output)
    invariant output == a[..ai] + b[..bi]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
  {
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
    }
    assert IsSorted(output);
    assert multiset(output) == multiset(a[..ai]) + multiset(b[..bi]);
  }
  assert multiset(output) == multiset(a) + multiset(b);
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  output := input;
}