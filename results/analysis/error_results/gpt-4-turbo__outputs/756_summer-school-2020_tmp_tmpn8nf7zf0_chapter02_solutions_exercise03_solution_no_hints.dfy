predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

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
  invariant IsSorted(output)
  invariant multiset(output) + multiset(a[ai..]) + multiset(b[bi..]) == multiset(a+b)
  invariant 0 <= ai <= |a|
  invariant 0 <= bi <= |b|
  decreases |a| - ai + |b| - bi
  {
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
    }
  }
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  if |input| == 0 {
    output := [];
  } else {
    var sorted := merge_sort(input);
    output := sorted;
    assert SortSpec(input, output); // Explicitly assert the postcondition to ensure it is met.
  }
}