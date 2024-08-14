
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: array<int> := new int[arr.Length](i requires 0 <= i < arr.Length :: 0);
  var count := 0;

  for i := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] in arr[..]
    invariant forall j :: 0 <= j < count ==> evenList[j] % 2 == 0
    invariant forall j :: 0 <= j < count ==> evenList[j] in evenNumbers[..]
    invariant forall j :: 0 <= j < count ==> exists n :: 0 <= n < arr.Length && evenList[j] == arr[n]
  {
    if arr[i]%2==0
    {
      evenList[count] := arr[i];
      count := count + 1;
    }
  }

  evenNumbers := new int[count](i requires 0 <= i < count :: evenList[i]);
}
