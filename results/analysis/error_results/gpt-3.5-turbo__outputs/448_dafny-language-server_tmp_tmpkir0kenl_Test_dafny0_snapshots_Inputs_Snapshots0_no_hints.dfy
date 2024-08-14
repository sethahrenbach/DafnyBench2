method foo()
{
  bar();
}

method bar()
  ensures false;
{
  assert false;
  return;
}