
module Foo

function Bar(x: int): int
  requires 0 <= x && x < 10
  ensures 0 <= result && result < 10
{
  if x < 5 then 0 else 1 + Bar(x - 5)
}

function Baz(x: int): int
  requires 0 <= x && x < 10
  ensures 0 <= result && result < 10
{
  if x < 5 then 0 else 1 + Baz(x - 5)
}

lemma BarBaz(x: int):
  requires 0 <= x && x < 10
  ensures Bar(x) == Baz(x)
{
  if x < 5 then
    assert Bar(x) == Baz(x);
  else
    assert Bar(x) == Baz(x);
}
