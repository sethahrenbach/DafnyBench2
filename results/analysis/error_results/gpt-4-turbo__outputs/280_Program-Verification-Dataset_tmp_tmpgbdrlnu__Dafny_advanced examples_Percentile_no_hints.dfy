// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{
  if end == -1 then
    0.0
  else
    A[end] + SumUpto(A, end-1)
}

function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length-1)
}

method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
{
  i := -1;
  var s: real := 0.0;

  while i+1 < A.Length && s + A[i+1] <= (p/100.0) * total
    invariant -1 <= i < A.Length
    invariant s == SumUpto(A, i)
    invariant forall j | 0 <= j <= i :: A[j] > 0.0
    invariant s <= (p/100.0) * total
  {
    i := i + 1;
    s := s + A[i];
  }
  // Ensure the postconditions are met
  assert s == SumUpto(A, i);
  assert i == -1 || SumUpto(A, i) <= (p/100.0) * total;
  assert i+1 >= A.Length || SumUpto(A, i+1) > (p/100.0) * total;
}

// example showing that, with the original postcondition, the answer is non-unique!
method PercentileNonUniqueAnswer() returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0

  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= (p/100.0) * total
  ensures i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= (p/100.0) * total
  ensures i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total

  ensures i1 != i2
{
  p := 100.0;
  A := new real[1];
  A[0] := 1.0;
  total := 1.0;
  i1 := -1;
  i2 := 0;
}

// proof that, with the corrected postcondition, the answer is unique
lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0

  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= (p/100.0) * total
  requires i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= (p/100.0) * total
  requires i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total

  ensures i1 == i2
{
  if i1 != i2 {
    assert SumUpto(A, i1) < SumUpto(A, i2) || SumUpto(A, i2) < SumUpto(A, i1);
  }
}
