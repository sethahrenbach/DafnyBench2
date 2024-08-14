
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while idx < Array.Length
    invariant 0 <= idx <= Array.Length
    invariant forall k | 0 <= k < idx :: Array[k] <= Array[idx]
    invariant forall k | idx <= k < Array.Length :: Array[idx] <= Array[k]
    invariant multiset(old(Array[..])) == multiset(Array[..])
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while idx' < Array.Length
      invariant idx <= minIndex < Array.Length
      invariant idx < idx' <= Array.Length
      invariant forall k | idx <= k < idx' :: Array[k] >= Array[minIndex]
      invariant forall k | idx' <= k < Array.Length :: Array[minIndex] <= Array[k]
      invariant multiset(old(Array[..])) == multiset(Array[..])
    {
      if Array[idx'] < Array[minIndex] {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    idx := idx + 1;
  }
}
