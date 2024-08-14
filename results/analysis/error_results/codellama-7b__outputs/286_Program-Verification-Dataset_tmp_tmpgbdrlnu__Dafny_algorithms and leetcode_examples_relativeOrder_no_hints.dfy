
predicate IsEven(n: int)
{
  n % 2 == 0
}

method FindEvenNumbers(arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var evenList: seq<int> := [];
    ghost var indices: seq<int> := [];

    for i := 0 to arr.Length
           exists n, m :: 0 <= n < m < i && evenList[k] == arr[n] && evenList[l] == arr[m]
    {
        if IsEven(arr[i])
        {
          evenList := evenList + [arr[i]];
          indices := indices + [i];
        }
    }

    // Add a loop invariant to ensure that the loop terminates
    loop invariant 0 <= i <= arr.Length;

    // Add an assertion to ensure that the loop body is executed at most once for each element in the array
    assert 0 <= i < arr.Length ==> evenList.Length <= arr.Length;

    // Add an assertion to ensure that the loop body is executed at most once for each element in the array
    assert 0 <= i < arr.Length ==> indices.Length <= arr.Length;

    // Add an assertion to ensure that the loop body is executed at most once for each element in the array
    assert 0 <= i < arr.Length ==> evenList.Length == indices.Length;

    // Add an assertion to ensure that the loop body is executed at most once for each element in the array
    assert 0 <= i < arr.Length ==> evenList[i] == arr[i];

    // Add an assertion to ensure that the loop body is executed at most once for each element in the array
    assert 0 <= i < arr.Length ==> indices[i] == i;

    evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);
}
