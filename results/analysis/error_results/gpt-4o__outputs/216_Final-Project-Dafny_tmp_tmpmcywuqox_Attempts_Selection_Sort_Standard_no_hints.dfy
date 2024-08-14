method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
    invariant 0 <= idx <= Array.Length
    invariant multiset(old(Array[..])) == multiset(Array[..])
    invariant forall i, j :: 0 <= i < j < idx ==> Array[i] <= Array[j]
    invariant forall i :: 0 <= i < idx ==> exists j :: 0 <= j < Array.Length && Array[i] == old(Array[j])
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
      invariant idx <= minIndex < Array.Length
      invariant idx <= idx' <= Array.Length
      invariant forall k :: idx <= k < idx' ==> Array[minIndex] <= Array[k]
      invariant forall k :: idx <= k < idx' ==> exists j :: idx <= j < idx' && Array[k] == old(Array[j])
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