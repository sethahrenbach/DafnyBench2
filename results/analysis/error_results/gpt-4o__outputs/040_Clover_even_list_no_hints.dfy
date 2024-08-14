method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant evenList == [arr[j] | j <- 0..i, arr[j] % 2 == 0]
    invariant indices == [j | j <- 0..i, arr[j] % 2 == 0]
    invariant forall k :: 0 <= k < |evenList| ==> evenList[k] % 2 == 0
    invariant forall k, l :: 0 <= k < l < |evenList| ==>
                           exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m]
  {
    if arr[i] % 2 == 0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
    i := i + 1;
  }

  evenNumbers := new int[|evenList|](i => evenList[i]);
}