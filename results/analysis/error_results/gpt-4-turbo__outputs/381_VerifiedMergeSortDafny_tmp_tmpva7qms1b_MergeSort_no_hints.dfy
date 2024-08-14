
predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
{
  forall i :: start <= i < end ==> a[i] <= a[i+1]
}

predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  requires 0 <= start <= end <= b.Length
  requires end - start == |a1| + |a2|
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start + 1
  ensures sorted_slice(b, start, end)
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;

  while k <= end
    invariant start <= k <= end
    invariant sorted_slice(b, start, k-1)
    invariant a1Pos + a2Pos == k - start
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant multiset(a1[0..a1Pos]) + multiset(a2[0..a2Pos]) == multiset(b[start..k])
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < b.Length
  ensures sorted_slice(b, start, end)
  ensures merged(a1, a2, b, start, end)
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k <= end
    invariant start <= k <= end
    invariant sorted_slice(b, start, k-1)
    invariant a1Pos + a2Pos == k - start
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant multiset(a1[0..a1Pos]) + multiset(a2[0..a2Pos]) == multiset(b[start..k])
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}
