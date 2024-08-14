method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
    invariant 0 <= idx <= Array.Length
    invariant forall k :: 0 <= k < idx ==> Array[k] <= Array[idx-1]
    invariant forall k :: idx <= k < Array.Length ==> exists j :: idx <= j < Array.Length && Array[j] == old(Array[k])
    invariant multiset(Array[..]) == multiset(old(Array[..]))
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
      invariant idx <= minIndex < Array.Length
      invariant idx < idx' <= Array.Length
      invariant forall j :: idx <= j < idx' ==> Array[minIndex] <= Array[j]
      invariant forall j :: idx <= j < idx' ==> exists k :: idx <= k < Array.Length && Array[j] == old(Array[k])
      invariant multiset(Array[idx..idx']) == multiset(old(Array[idx..idx']))
      invariant forall j :: idx <= j < idx' ==> Array[minIndex] <= Array[j]
    {
      if (Array[idx'] < Array[minIndex]) {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    idx := idx + 1;
  }
}