type T = int // example

method partition(a: array<T>) returns(pivotPos: int) 
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
    ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
    modifies a
{
    pivotPos := a.Length - 1; // chooses pivot at end of array 
    var i := 0;  // index that separates values smaller than pivot (0 to i-1), 
                 // and values greater or equal than pivot (i to j-1) 
    var j := 0;  // index to scan the array
 
    // Scan the array and move elements as needed
    while  j < a.Length 
      invariant 0 <= i <= j <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] < a[pivotPos]
      invariant forall k :: j < k < a.Length ==> a[k] >= a[pivotPos]
    {
      if a[j] < a[pivotPos] {
        a[i], a[j] := a[j], a[i];
        i := i + 1;
      }
      j := j+1;
    }
 
    // Swap pivot to the 'mid' of the array
    assert forall k :: 0 <= k < pivotPos ==> a[k] < a[pivotPos];
    assert forall k :: pivotPos < k < a.Length ==> a[k] >= a[pivotPos];
    assert multiset(a[..]) == multiset(old(a[..]));
    a[a.Length-1], a[i] := a[i], a[a.Length-1];
    pivotPos := i;  

    assert forall k :: 0 <= k < pivotPos ==> a[k] < a[pivotPos];
    assert forall k :: pivotPos < k < a.Length ==> a[k] >= a[pivotPos];
    assert multiset(a[..]) == multiset(old(a[..]));
}