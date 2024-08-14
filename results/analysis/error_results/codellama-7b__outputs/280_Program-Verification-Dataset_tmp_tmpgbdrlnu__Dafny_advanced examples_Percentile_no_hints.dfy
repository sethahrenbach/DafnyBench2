
function Sum(A: array<real>): real
  requires 0 <= A.Length <= 100
  requires forall i in 0..A.Length: A[i] >= 0
  ensures 0 <= result <= 100
{
  var sum: real := 0;
  for i in 0..A.Length {
    sum := sum + A[i];
  }
  return sum;
}
