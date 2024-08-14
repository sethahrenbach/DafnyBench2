method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  for i := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> (arr[j] % 2 == 0) <==> (arr[j] in evenList)
    invariant forall j :: 0 <= j < i ==> (arr[j] % 2 != 0) ==> (arr[j] !in evenList)
    invariant forall j :: 0 <= j < |evenList| ==> evenList[j] % 2 == 0
    invariant |evenList| == |indices|
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < i
    invariant forall j :: 0 <= j < |indices| ==> arr[indices[j]] == evenList[j]
  {
    if arr[i] % 2 == 0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }

  evenNumbers := new int[|evenList|];
  for j := 0 to |evenList| - 1
    invariant 0 <= j <= |evenList|
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] == evenList[k]
  {
    evenNumbers[j] := evenList[j];
  }
}