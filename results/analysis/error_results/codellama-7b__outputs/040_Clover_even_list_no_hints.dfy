
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenList: seq<int> := [];
  ghost var indices: seq<int> := [];

  for i := 0 to arr.Length
  {
    if arr[i]%2==0
    {
      evenList := evenList + [arr[i]];
      indices := indices + [i];
    }
  }

  evenNumbers := new int[|evenList|](i requires 0 <= i < |evenList| => evenList[i]);

  // loop invariant: evenList contains only even numbers
  // loop invariant: indices contains only indices of even numbers in arr
  // loop invariant: evenNumbers contains only even numbers from arr
  // loop invariant: evenNumbers is sorted in increasing order
  // loop invariant: evenNumbers has the same length as evenList
  // loop variant: |evenList|

  // postcondition: evenNumbers contains only even numbers from arr
  // postcondition: evenNumbers is sorted in increasing order
  // postcondition: evenNumbers has the same length as evenList

  // assert: forall i in 0..|evenList|-1 :: evenList[i] % 2 == 0
  // assert: forall i in 0..|evenList|-1 :: indices[i] < arr.Length
  // assert: forall i in 0..|evenList|-1 :: evenNumbers[i] == arr[indices[i]]
  // assert: forall i in 0..|evenList|-2 :: evenNumbers[i] < evenNumbers[i+1]
}
