method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
  modifies X;
  requires X.Length >= 1 && n == X.Length;
  ensures b >= n;
  ensures forall x :: 0 <= x < a < n ==> X[x] <= p;
  ensures forall x :: a == n || (0 <= a <= x < n ==> X[x] > p);
  ensures multiset(X[..]) == multiset(old(X[..]))
{
  a := 0;
  b := n;

  while a < b
    invariant 0 <= a <= b <= n;
    invariant forall x :: 0 <= x < a ==> X[x] <= p;
    invariant forall x :: a <= x < b ==> X[x] <= p;
    invariant forall x :: b <= x < n ==> X[x] > p;
  {
    if X[a] <= p {
      a := a + 1;
    } else {
      b := b - 1;
      var t := X[b];
      X[b] := X[a];
      X[a] := t;
    }
  }
}
