
method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  ensures sorted_slice(b, start, end)
  ensures merged(a1, a2, b, start, end)
{
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos]
    {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    }
    else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos]
    {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    else if a1Pos < |a1|
    {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    }
    else
    {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
}

predicate sorted_seq(seq<int> s)
  requires 0 <= i < |s| ==> s[i] <= s[i+1]
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate sorted_slice(array<int> a, int start, int end)
  requires 0 <= start <= end <= |a|
  requires sorted_seq(a[start..end])
{
  forall i, j :: 0 <= i < j < |a| && start <= i < j < end ==> a[i] <= a[j]
}

predicate merged(seq<int> a1, seq<int> a2, array<int> b, int start, int end)
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  ensures sorted_slice(b, start, end)
{
  forall i, j :: 0 <= i < j < |a1| && start <= i < j < end ==> a1[i] <= a1[j]
  forall i, j :: 0 <= i < j < |a2| && start <= i < j < end ==> a2[i] <= a2[j]
  forall i, j :: 0 <= i < j < |b| && start <= i < j < end ==> b[i] <= b[j]
}
