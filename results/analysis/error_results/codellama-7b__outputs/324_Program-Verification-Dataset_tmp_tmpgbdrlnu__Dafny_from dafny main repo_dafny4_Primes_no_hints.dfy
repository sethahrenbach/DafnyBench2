
function foo(n: int) returns (result: int)
  ensures result == n * n;
{
  var i: int := 0;
  while i < n {
    i := i + 1;
  }
  return i * i;
}
