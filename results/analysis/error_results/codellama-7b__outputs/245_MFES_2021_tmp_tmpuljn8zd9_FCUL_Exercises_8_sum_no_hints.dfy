
function calcSum(n: nat) : nat
{
  var s := 0;
  var i := 0;
  while i < n
  {
    s := s + i;
    i := i + 1;
  }
  return s;
}

method sum(n: nat) returns(s: nat)
  ensures s == calcSum(n + 1)
{
  s := calcSum(n + 1);
}
