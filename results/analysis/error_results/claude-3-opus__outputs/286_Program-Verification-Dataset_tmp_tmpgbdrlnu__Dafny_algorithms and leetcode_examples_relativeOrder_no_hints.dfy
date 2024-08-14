predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var evenList: seq<int> := [];
    ghost var indices: seq<int> := [];

    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant |evenList| == |indices|
      invariant forall j :: 0 <= j < |evenList| ==> evenList[j] in arr[..] && IsEven(evenList[j])
      invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < i && arr[indices[j]] == evenList[j]
      invariant forall k, l :: 0 <= k < l < |evenList| ==>
        exists n, m :: 0 <= n < m < |indices| && indices[n] < indices[m] && evenList[k] == arr[indices[n]] && evenList[l] == arr[indices[m]]
    {
        if i < arr.Length && IsEven(arr[i])
        {
          evenList := evenList + [arr[i]];
          indices := indices + [i];
        }
    }

    evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
    
    // Prove postconditions
    forall x | x in arr[..] && IsEven(x)
      ensures x in evenNumbers[..]
    {
      var j :| 0 <= j < |evenList| && evenList[j] == x;
    }
    
    forall x | x !in arr[..]
      ensures x !in evenNumbers[..]
    {
      assert forall j :: 0 <= j < |evenList| ==> evenList[j] in arr[..];
    }
    
    forall k, l | 0 <= k < l < evenNumbers.Length
      ensures exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
    {
      var n :| 0 <= n < |indices| && evenList[k] == arr[indices[n]];
      var m :| n < m < |indices| && evenList[l] == arr[indices[m]];
      assert indices[n] < indices[m];
    }
}