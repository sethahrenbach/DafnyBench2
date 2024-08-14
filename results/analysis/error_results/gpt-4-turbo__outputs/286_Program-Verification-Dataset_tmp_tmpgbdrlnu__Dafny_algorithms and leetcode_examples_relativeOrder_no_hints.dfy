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

    for i := 0 to arr.Length - 1
      invariant 0 <= i < arr.Length
      invariant forall k, l :: 0 <= k < l < |evenList| ==>
        exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m]
      invariant forall x :: x in arr[..i] && IsEven(x) ==> x in evenList
      invariant forall x :: x in evenList ==> x in arr[..i] && IsEven(x)
      invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
      invariant |indices| == |evenList|
      invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < i
      invariant forall k, j :: 0 <= k < j < |indices| ==> indices[k] < indices[j]
    {
        if IsEven(arr[i])
        {
          evenList := evenList + [arr[i]];
          indices := indices + [i];
        }
    }

    evenNumbers := new int[|evenList|];
    for j := 0 to |evenList| - 1
      invariant 0 <= j <= |evenList|
      invariant forall x :: x in arr[..] && IsEven(x) ==> x in evenList[..j]
      invariant forall x :: x in evenList[..j] ==> x in arr[..] && IsEven(x)
      invariant forall k, l :: 0 <= k < l < j ==>
        exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
    {
        evenNumbers[j] := evenList[j];
    }
}