
function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    assert 0 < 1; // More(0) is 1
  } else {
    Increasing(x - 2);
    assert x - 2 < More(x - 2);
    assert x < More(x - 2) + 3;
  }
}

method ExampleLemmaUse(a: int) {
  var b := More(a);
  Increasing(a);
  var c := More(b);
  Increasing(b);
}

method ExampleLemmaUse50(a: int) {
  Increasing(a);
  var b := More(a);
  var c := More(b);
  if a < 1000 {
    Increasing(b);
  }
}

method ExampleLemmaUse51(a: int) {
  Increasing(a);
  var b := More(a);
  Increasing(b);
  b := More(b);
  if a < 1000 {
    Increasing(b);
  }
}

function Ack(m: nat, n: nat): nat {
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{
  if n == 0 {
    assert Ack(1, 0) == 2;
  } else {
    Ack1n(1, n - 1);
    assert Ack(1, n) == n + 2;
  }
}

function Reduce(m: nat, x: int): int {
  if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{
  if m == 0 {
    assert Reduce(0, x) == x;
  } else {
    ReduceUpperBound(m / 2, x + 1);
    assert Reduce(m / 2, x + 1) <= x + 1;
    assert Reduce(m, x) <= x;
  }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  if m == 0 {
    assert x - 2 * 0 <= Reduce(0, x);
  } else {
    ReduceLowerBound(m / 2, x + 1);
    assert x + 1 - 2 * (m / 2) <= Reduce(m / 2, x + 1);
    assert x - 2 * m <= Reduce(m, x);
  }
}
