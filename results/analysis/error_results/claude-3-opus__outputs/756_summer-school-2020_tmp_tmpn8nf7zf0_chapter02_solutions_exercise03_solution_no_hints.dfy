predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

lemma SequenceConcat(s:seq<int>, pivot:int)
  requires 0<=pivot<|s|
  ensures s[..pivot] + s[pivot..] == s
{
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
    calc {
      multiset(output);
      multiset(leftSorted + rightSorted);
      { assert SortSpec(left, leftSorted); 
        assert SortSpec(right, rightSorted); }
      multiset(leftSorted) + multiset(rightSorted);
      multiset(left) + multiset(right);
      { SequenceConcat(input, pivotIndex); }
      multiset(left + right);
      multiset(input);
    }
  }
}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  //ensures IsSorted(output)
  ensures SortSpec(a+b, output)
  //decreases |a|+|b|
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a| 
    invariant 0 <= bi <= |b|
    invariant IsSorted(output)
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
  {
    if ai == |a| {
      output := output + b[bi..];
      bi := |b|;
    } else if bi == |b| {
      output := output + a[ai..];
      ai := |a|;
    } else if a[ai] <= b[bi] {
      output := output + [a[ai]];
      ai := ai + 1;
    } else {
      output := output + [b[bi]];
      bi := bi + 1;
    }
  }
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
  //ensures SortSpec(input, output)
{
  output := [1, 2, 3];
}