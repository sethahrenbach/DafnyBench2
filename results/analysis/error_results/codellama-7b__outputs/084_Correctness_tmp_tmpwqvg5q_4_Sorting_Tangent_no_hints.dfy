
method foo(x: int)
  ensures x >= 0
{
  if x < 0 then
    assert false;
  else
    assert x >= 0;
}
