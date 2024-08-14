
method lookForMin (a: array<int>, i: int) returns (m: int)
  ensures i <= m < a.Length
  ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  var j := i;
  m := i;
  while(j < a.Length)
  {
    if(a[j] < a[m]) { m := j; }
    j := j + 1;
  }
}
