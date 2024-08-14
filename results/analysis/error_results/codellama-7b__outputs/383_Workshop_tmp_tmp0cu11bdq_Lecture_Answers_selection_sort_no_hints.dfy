
method SelectionSort(a: array<int>)
  modifies a
  ensures sorted(a)
{
  var n := a.Length;
  while (n > 0)
  {
    var min := n - 1;
    var i := 0;
    while (i < n)
    {
      if (a[i] < a[min])
      {
        min := i;
      }
      i := i + 1;
    }
    a[n], a[min] := a[min], a[n];
    n := n - 1;
  }
}
