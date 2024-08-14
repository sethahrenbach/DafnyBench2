predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}


method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
{  
  var high := 1;
  while (high < Array.Length) 
    invariant 1 <= high <= Array.Length
    invariant InsertionSorted(Array, 0, high)
  {  
    var low := high-1;
    assert 0 <= low < high <= Array.Length;
    while low >= 0 && Array[low+1] < Array[low]
      invariant -1 <= low < high
      invariant high <= Array.Length
      invariant forall i,j :: 0 <= i < j <= low ==> Array[i] <= Array[j]
      invariant forall i :: low+1 <= i < high ==> Array[low+1] <= Array[i]
    {
      Array[low], Array[low+1] := Array[low+1], Array[low];
      low := low-1;
    }
    assert low == -1 ==> InsertionSorted(Array, 0, high+1);
    assert low >= 0 ==> InsertionSorted(Array, 0, low+1) && InsertionSorted(Array, low+1, high+1) && Array[low] <= Array[low+1];
    high := high+1;       
  }
}