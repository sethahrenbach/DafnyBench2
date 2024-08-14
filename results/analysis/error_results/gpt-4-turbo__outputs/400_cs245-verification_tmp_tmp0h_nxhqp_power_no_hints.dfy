//power -- Stephanie Renee McIntyre
//Based on the code used in the course overheads for Fall 2018

//There is no definition for power, so this function will be used for validating that our imperative program is correct.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= a && 0 <= n;

//Our code from class
method compute_power(a: int, n: int) returns (s: int)
/*Pre-Condition*/   requires n >= 0 && a >= 0;
/*Post-Condition*/  ensures s == power(a,n);
{
  s := 1;
  var i := 0; 
  while (i < n)
    invariant s == power(a, i) && i <= n && 0 <= i
    decreases n - i
  {
    s := s * a;
    i := i + 1;
  }
}