
function countTo(a: array<bool>, n: int): int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

method CountTrue(a: array<bool>): int
  requires a != null;
  ensures result == countTo(a, a.Length);
{
  result := 0;
  for i := 0 to a.Length
  {
    // Loop Invariant: result == countTo(a, i)
    if a[i] {
      result := result + 1;
    }
  }
  // Assert statement: result == countTo(a, a.Length)
  assert result == countTo(a, a.Length);
}
