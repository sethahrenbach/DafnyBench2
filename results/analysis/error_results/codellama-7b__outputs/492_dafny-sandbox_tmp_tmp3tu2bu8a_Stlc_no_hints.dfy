
function factorial(n: int): int
  ensures factorial(n) == n!
{
  if n == 0 then
    1
  else
    n * factorial(n-1)
}
