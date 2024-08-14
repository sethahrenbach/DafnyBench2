method sort(A: array<int>, n: int)
  modifies A
  requires n == A.Length
  requires n >= 0
  ensures forall i,j :: 0 <= i <= j < n ==> A[i] <= A[j]
{
  var k := 0;
  while(k < n)
    invariant 0 <= k <= n
    invariant forall i :: 0 <= i < k ==> A[i] == i
  {
    A[k] := k;
    k := k + 1;
  }
}