// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

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
    invariant 0 <= r <= n
    invariant u == Factorial(r)
  {
    var v := u;
    var s := 1;
    while (s <= r)
      invariant 1 <= s <= r + 1
      invariant u == Factorial(r) + (s - 1) * v
    {
      u := u + v;
      s := s + 1;
    }
    assert u == Factorial(r) + r * Factorial(r) == (r + 1) * Factorial(r) == Factorial(r + 1);
    r := r + 1;
  }
}

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
{
  var m, n := 0, N-1;
  while (m < n)
    invariant 0 <= m <= f <= n < N
    invariant forall p :: 0 <= p < m ==> A[p] <= A[f]
    invariant forall q :: n < q < N ==> A[f] <= A[q]
    invariant forall p,q :: 0 <= p <= m <= q <= n ==> A[p] <= A[q]
    invariant forall p,q :: m <= p <= f <= q <= n ==> A[p] <= A[q]
  {
    var r, i, j := A[f], m, n;
    while (i < j)
      invariant m <= i <= f <= j <= n
      invariant forall p :: 0 <= p < m ==> A[p] <= r
      invariant forall q :: n < q < N ==> r <= A[q]
      invariant forall p :: m <= p < i ==> A[p] <= r
      invariant forall q :: j < q <= n ==> r <= A[q]
      invariant forall p,q :: m <= p < i <= q < j ==> A[p] <= A[q]
      invariant forall p,q :: i <= p < j <= q <= n ==> A[p] <= A[q]
      // the following two invariants capture (and follow from) the fact that the array is not modified outside the [m:n] range
      invariant forall k :: 0 <= k < m || n < k < N ==> A[k] == old(A[k])
      // the following invariant is used to prove progress of the outer loop
      invariant i > m || j < n || (i == m && j == n && m == f) 
    {
      ghost var firstIteration := i==m && j==n;
      while (A[i] < r)
        invariant m <= i <= f <= j <= n
        invariant forall p :: m <= p < i ==> A[p] <= r
      { i := i + 1; }

      while (r < A[j])
        invariant m <= i <= f <= j <= n
        invariant forall q :: j < q <= n ==> r <= A[q]
      { j := j - 1; }

      if (i < j) {
        A[i], A[j] := A[j], A[i];  // swap A[i] and A[j]
        i, j := i + 1, j - 1;
      }
    }

    if (f <= j) {
      n := j;
    } else if (i <= f) {
      m := i;
    } else {
      break;  // Hoare used a goto
    }
  }
}
