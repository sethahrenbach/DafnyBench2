
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
  requires Sorted(q) && HasAddends(q, x)
  ensures i < j < |q| && q[i] + q[j] == x
{
  i := 0;
  j := |q| - 1;
  var sum := q[i] + q[j];

  while sum != x
  {
    if (sum > x)
    {
      // Sum it too big, lower it by decreasing the high index
      LoopInvWhenSumIsBigger(q, x, i, j, sum);
      j := j - 1;
    }
    // 'sum == x' cannot occur because the loop's guard is 'sum != x'.
    else // (sum < x)
    {
      // Sum is too small, make it bigger by increasing the low index.
      i := i + 1;
    }

    sum := q[i] + q[j];
  }
}

predicate Sorted(q: seq<int>)
{
  forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
  exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
  requires HasAddends(q, x)
  requires Sorted(q)
  requires sum > x;
  ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
{
  HasAddends(q[i..(j + 1)], x)
}
