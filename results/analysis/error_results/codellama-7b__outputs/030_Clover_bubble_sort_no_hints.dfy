
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  // Loop invariant: a[0..i] is sorted
  var i := a.Length - 1;
  while (i > 0)
  {
    // Loop invariant: a[0..i] is sorted and a[j] <= a[j+1] for all j in [0..i]
    var j := 0;
    while (j < i)
    {
      // Invariant: a[0..i] is sorted and a[j] <= a[j+1] for all j in [0..i]
      if (a[j] > a[j + 1])
      {
        // Invariant: a[0..i] is sorted and a[j] <= a[j+1] for all j in [0..i]
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    // Invariant: a[0..i] is sorted and a[i] <= a[i+1]
    i := i - 1;
  }
  // Invariant: a[0..i] is sorted and a[i] <= a[i+1]
}
