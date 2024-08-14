//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785

predicate sorted(a: array<int>, from: int, to: int)
  requires 0 <= from <= to <= a.Length;
  reads a;
{
  forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

predicate pivot(a: array<int>, to: int, pvt: int)
  requires 0 <= pvt < to <= a.Length;
  reads a;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y]
}

method BubbleSort(a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i := 1;
  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := i;
    while (j > 0)
      invariant 0 <= j <= i
      invariant sorted(a, 0, j)
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j-1]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if (a[j-1] > a[j]) {
        a[j - 1], a[j] := a[j], a[j - 1];
      }
      j := j - 1;
    }
    i := i + 1;
  }
}