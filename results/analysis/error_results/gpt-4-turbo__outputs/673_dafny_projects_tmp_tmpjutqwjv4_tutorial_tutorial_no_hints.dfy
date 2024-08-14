
// Working through https://dafny.org/dafny/OnlineTutorial/guide

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (ret: nat)
  ensures ret == fib(n)
{
  var a := 0;
  var b := 1;
  var i := 0;
  while i < n
    invariant i <= n
    invariant a == fib(i)
    invariant b == fib(i+1)
  {
    a, b := b, a+b;
    i := i + 1;
  }
  ret := a;
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> (forall k :: 0 <= k < a.Length ==> a[k] != key)
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key {
      return index;
    }
    index := index + 1;
  }
  return -1;
}

predicate sorted(a: array<int>)
  reads a
{
  forall n, m :: 0 <= n < m < a.Length ==> a[n] <= a[m]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low := 0;
  var high := a.Length - 1;
  while low <= high
    invariant 0 <= low <= high + 1 <= a.Length
    invariant forall k :: 0 <= k < low || high < k < a.Length ==> a[k] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if a[mid] > value {
      high := mid - 1;
    } else {
      return mid;
    }
  }
  return -1;
}
