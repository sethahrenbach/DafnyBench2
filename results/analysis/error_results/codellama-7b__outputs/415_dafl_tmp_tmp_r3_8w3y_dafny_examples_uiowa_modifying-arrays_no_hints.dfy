  method CopyArray<T>(a: array<T>, b: array<T>)
  requires a.Length == b.Length
  modifies b
{
  var n := 0;
  while n < a.Length {
    b[n] := a[n];
    n := n + 1;
  }
}