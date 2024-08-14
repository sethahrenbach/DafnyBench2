
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false

ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method AdditiveFactorial(n: nat) returns (u: nat)
  ensures u == Factorial(n);
{
  u := 1;
  var r := 0;
  while (r < n)
    invariant 0 <= r <= n;
    invariant u == Factorial(n) / Factorial(n - r);
  {
    var v := u;
    var s := 1;
    while (s <= r)
      invariant 1 <= s <= r + 1;
      invariant u == v * Factorial(r - s + 1);
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
}

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{
  var m, n := 0, N-1;
  while (m < n)
    invariant 0 <= m <= n <= N;
    invariant forall k :: m <= k < n ==> A[k] != A[f];
  {
    var r, i, j := A[f], m, n;
    while (i <= j)
      invariant m <= i <= j <= n;
      invariant forall k :: m <= k < i ==> A[k] < r;
      invariant forall k :: j < k <= n ==> r < A[k];
    {
      ghost var firstIteration := i==m && j==n;
      while (i <= j && A[i] < r)
        invariant m <= i <= j + 1;
        invariant forall k :: m <= k < i ==> A[k] < r;
      {
        i := i + 1;
      }

      while (i <= j && r < A[j])
        invariant m <= j <= n;
        invariant forall k :: j < k <= n ==> r < A[k];
      {
        j := j - 1;
      }

      if (i <= j) {
        var w := A[i]; A[i] := A[j]; A[j] := w;  // swap A[i] and A[j] (which may be referring to the same location)
        i, j := i + 1, j - 1;
      }
    }

    if (f <= j) {
      n := j;
    } else if (i <= f) {
      m := i;
    } else {
      assert forall k :: m <= k < n ==> A[k] != A[f];  // Hoare used a goto
    }
  }
}
