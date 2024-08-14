method M()
{
  // Since N() must ensure P(), and P() is always false, we need to make this method unreachable
  return;
}

method N()
  ensures P();
{
  // Since P() is always false, this method cannot ensure P()
  // Therefore, we need to make this method unreachable
  return;
}

predicate P()
{
  false
}