
function F(x: nat, ghost y: nat) returns (res: nat)
  ensures res == 13 * x
{
  if x == 0 then
    0
  else if y != 0
    ensures F(x, y - 1) == 13 * x;
    F(x, y - 1)
  else
    ensures F(x - 1, 60) + 13 == 13 * x;
    F(x - 1, 60) + 13
}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

function G(x: nat, ghost y: nat) returns (res: nat)
  ensures res == 13 * x
{
  if x == 0 then
    0
  else if y != 0
    ensures G(x, y - 1) == 13 * x;
    var z := x + x;
    var a := 100;
    var b := if x < z then G(x, y - 1) else G(x, y - 1);
    var c := 200;
    b
  else
    ensures G(x - 1, 60) + 13 == 13 * x;
    G(x - 1, 60) + 13
}

function H(x: int, ghost y: nat) returns (res: int)
  ensures res == x
{
  if y == 0 then
    x
  else
    ensures H(x, y - 1) == x;
    H(x, y - 1)
}

function J(x: int) returns (res: int)
  ensures res == x
{
  if true then
    x
  else
    J(x)
}

function K(x: int, ghost y: nat) returns (res: int)
{
  K(x, y - 1)
}

method Main() {
  print F(5, 3), "\n"; // 65
  print G(5, 3), "\n"; // 65
  print H(65, 3), "\n"; // 65
  print J(65), "\n"; // 65
}
