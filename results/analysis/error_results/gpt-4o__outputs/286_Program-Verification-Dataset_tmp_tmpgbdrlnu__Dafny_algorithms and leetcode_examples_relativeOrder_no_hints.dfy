predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var evenList: seq<int> := [];
    ghost var indices: seq<int> := [];

    var i: int := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant evenList == [arr[j] | j <- 0..i, IsEven(arr[j])]
      invariant |indices| == |evenList|
      invariant forall k, l :: 0 <= k < l < |evenList| ==>
        exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m]
    {
        if IsEven(arr[i])
        {
          evenList := evenList + [arr[i]];
          indices := indices + [i];
        }
        i := i + 1;
    }

    evenNumbers := new int[|evenList|](i => evenList[i]);
}