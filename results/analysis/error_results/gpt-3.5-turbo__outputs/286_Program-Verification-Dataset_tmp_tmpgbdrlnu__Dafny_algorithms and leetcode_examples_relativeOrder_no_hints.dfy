predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..];
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var evenList: array<int> := new int[arr.Length];
    var indices: array<int> := new int[arr.Length];
    var count := 0;

    var i := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length;
      invariant forall k :: 0 <= k < count ==> evenList[k] in arr[..i];
      invariant forall k :: 0 <= k < count ==> indices[k] < i;
      invariant forall k, l :: 0 <= k < l < count ==>
        exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m];
      decreases arr.Length - i;
    {
        if IsEven(arr[i])
        {
          evenList[count] := arr[i];
          indices[count] := i;
          count := count + 1;
        }
        i := i + 1;
    }

    evenNumbers := new int[count](j requires 0 <= j < count => evenList[j]);
}