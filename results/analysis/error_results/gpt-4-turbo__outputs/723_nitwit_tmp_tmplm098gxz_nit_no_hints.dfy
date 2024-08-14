
predicate valid_base(b: nat) {
  b >= 2
}

predicate nitness(b: nat, n: nat)
  requires valid_base(b)
{
  0 <= n < b
}

method nit_increment(b: nat, n: nat) returns (sum: nat, carry: nat)
  requires valid_base(b)
  requires nitness(b, n)
  ensures nitness(b, sum)
  ensures carry == 0 || carry == 1
{
  sum := (n + 1) % b;
  carry := (n + 1) / b;
}

predicate is_max_nit(b: nat, q: nat) {
  q == b - 1
}

method max_nit(b: nat) returns (nmax: nat)
  requires valid_base(b)
  ensures nitness(b, nmax)
  ensures is_max_nit(b, nmax)
{
  nmax := b - 1;
}

method nit_flip(b: nat, n: nat) returns (nf: nat)
  requires valid_base(b)
  requires nitness(b, n)
  ensures nitness(b, nf)
{
  var mn: nat := max_nit(b);
  nf := mn - n;
}

method nit_add(b: nat, x: nat, y: nat) returns (z: nat, carry: nat)
  requires valid_base(b)
  requires nitness(b, x)
  requires nitness(b, y)
  ensures nitness(b, z)
  ensures carry == 0 || carry == 1
{
  z := (x + y) % b;
  carry := (x + y) / b;
}

method nit_add_three(b: nat, c: nat, x: nat, y: nat) returns (z: nat, carry: nat)
  requires valid_base(b)
  requires c == 0 || c == 1
  requires nitness(b, x)
  requires nitness(b, y)
  ensures nitness(b, z)
  ensures carry == 0 || carry == 1
{
  var sum, carry1 := nit_add(b, x, y);
  if (c == 1) {
    var sum2, carry2 := nit_add(b, sum, 1);
    z := sum2;
    carry := carry1 + carry2;
  } else {
    z := sum;
    carry := carry1;
  }
}

predicate bibble(b: nat, a: seq<nat>)
  requires valid_base(b)
  requires |a| == 4
  requires forall n :: n in a ==> nitness(b, n)
{
}

method bibble_add(b: nat, p: seq<nat>, q: seq<nat>) returns (r: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  requires bibble(b, q)
  ensures bibble(b, r)
{
  var z3, c3 := nit_add(b, p[3], q[3]);
  var z2, c2 := nit_add_three(b, c3, p[2], q[2]);
  var z1, c1 := nit_add_three(b, c2, p[1], q[1]);
  var z0, c0 := nit_add_three(b, c1, p[0], q[0]);

  r := [z0, z1, z2, z3];
}

method bibble_increment(b: nat, p: seq<nat>) returns (r: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, r)
{
  var q: seq<nat> := [0, 0, 0, 1];
  r := bibble_add(b, p, q);
}

method bibble_flip(b: nat, p: seq<nat>) returns (fp: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, fp)
{
  var n0 := nit_flip(b, p[0]);
  var n1 := nit_flip(b, p[1]);
  var n2 := nit_flip(b, p[2]);
  var n3 := nit_flip(b, p[3]);

  fp := [n0, n1, n2, n3];
}

method n_complement(b: nat, p: seq<nat>) returns (com: seq<nat>)
  requires valid_base(b)
  requires bibble(b, p)
  ensures bibble(b, com)
{
  var fp := bibble_flip(b, p);
  var fpi := bibble_increment(b, fp);
  com := fpi;
}

method Main() {
  var b := 3;
  var bibble1 := [2, 1, 0, 2];
  var complement := n_complement(b, bibble1);
  var bibble_sum := bibble_add(b, bibble1, complement);

  print bibble1, " + ", complement, " = ", bibble_sum, " (should be [0, 0, 0, 0])\n";
}
