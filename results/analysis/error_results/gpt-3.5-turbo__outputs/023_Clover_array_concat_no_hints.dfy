method concat(a:array<int>, b:array<int>) returns (c:array<int>)
  requires a != null && b != null
  requires a.Length + b.Length <= int.MaxValue
  ensures c.Length == b.Length + a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k + a.Length] == b[k]
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < c.Length
    invariant 0 <= i <= c.Length
    invariant forall k :: 0 <= k < i ==> (k < a.Length ==> c[k] == a[k]) && (k >= a.Length ==> c[k] == b[k - a.Length])
  {
    c[i] := if i < a.Length then a[i] else b[i - a.Length];
    i := i + 1;
  }
  c
}