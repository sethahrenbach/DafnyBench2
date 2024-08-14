
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
  while high < Array.Length 
    decreases Array.Length - high
    invariant 1 <= high <= Array.Length
    invariant InsertionSorted(Array, 0, high)
  {  
    var low := high-1;        
    while low >= 0 && Array[low+1] < Array[low]
      decreases low
      invariant 0 <= low < high
      invariant InsertionSorted(Array, 0, high)
    {
      assert InsertionSorted(Array, 0, high);
      Array[low], Array[low+1] := Array[low+1], Array[low];           
      low := low-1;       
      assert InsertionSorted(Array, 0, high+1);
      assert forall k :: 0 <= k < high+1 ==> InsertionSorted(Array, 0, k+1);
    }            
    high := high+1;       
  }
}  
