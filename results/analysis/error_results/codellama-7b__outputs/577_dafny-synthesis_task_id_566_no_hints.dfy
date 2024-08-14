
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumOfDigits(number)
{
  sum := 0;
  var n: nat := number;

  while n > 0
  {
    sum := sum + n % 10;
    n := n / 10;
  }

  return sum;
}
