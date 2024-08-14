
function sorted(a: array<int>, lo: int, hi: int): bool
  requires 0 <= lo <= hi <= a.Length
{
  var i := lo;
  while (i < hi)
  {
    if (a[i] > a[i + 1])
      return false;
    i := i + 1;
  }
  return true;
}
