method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
    invariant 0 <= idx <= Array.Length
    invariant multiset(old(Array[..])) == multiset(Array[..])
    invariant forall i, j :: 0 <= i < j < idx ==> Array[i] <= Array[j]
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
      invariant idx < idx' <= Array.Length
      invariant idx <= minIndex < Array.Length
      invariant forall i :: idx <= i < idx' ==> Array[minIndex] <= Array[i]
    {
      if (Array[idx'] < Array[minIndex]) {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    assert idx <= minIndex < Array.Length;
    assert forall i :: idx <= i < Array.Length ==> Array[minIndex] <= Array[i];
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    idx := idx + 1;
  }
}