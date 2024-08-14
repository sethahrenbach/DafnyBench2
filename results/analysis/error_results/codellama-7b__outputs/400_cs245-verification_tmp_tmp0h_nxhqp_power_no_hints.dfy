  I apologize for the confusion, and I will make sure to keep the preconditions and postconditions the same as the original program. Here is the corrected code:

function power(a: int, n: int): int
  requires 0 <= a && 0 <= n;
  ensures 0 <= result && result <= a^n;
{
  if n == 0 {
    return 1;
  } else {
    return a * power(a, n-1);
  }
}

I hope this corrected code passes the test.