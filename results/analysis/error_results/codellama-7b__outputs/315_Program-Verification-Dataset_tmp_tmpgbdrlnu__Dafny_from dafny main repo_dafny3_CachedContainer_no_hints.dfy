
module M1
{
  function f(x: int): int
  {
    if x < 0 then
      return 0;
    else
      return x;
  }
}

module M2
{
  import M1;

  function g(x: int): int
  {
    if x < 0 then
      return 0;
    else
      return x;
  }
}

module M3
{
  import M1;

  function h(x: int): int
  {
    if x < 0 then
      return 0;
    else
      return x;
  }
}

module Main
{
  import M1;
  import M2;
  import M3;

  function main(): int
  {
    return f(1) + g(2) + h(3);
  }
}
