
function foo(x: int, y: int): int
  requires x >= 0 && y >= 0
  ensures x + y == result
{
  return x + y;
}

function bar(x: int, y: int): int
  requires x >= 0 && y >= 0
  ensures x + y == result
{
  return x + y;
}

function main(): int
  requires true
  ensures result == 3
{
  var x: int := 1;
  var y: int := 2;
  var z: int := foo(x, y);
  var w: int := bar(x, y);
  return z + w;
}
