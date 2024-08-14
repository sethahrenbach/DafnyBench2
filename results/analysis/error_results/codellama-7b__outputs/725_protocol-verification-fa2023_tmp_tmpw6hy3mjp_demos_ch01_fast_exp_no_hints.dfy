
function foo(x: nat) returns (y: nat)
{
  if x == 0 then
    return 0;
  else if x == 1 then
    return 1;
  else
    return x + foo(x - 1);
  fi;
}
