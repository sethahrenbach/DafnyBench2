
function exp(b: nat, n: nat) returns (result: nat)
  ensures result == b^n
{
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    return;
  } else {
    exp_sum(b, n1-1, n2);
  }
}

lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  forall n1: nat, n2: nat
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2) {
    exp_sum(b, n1, n2);
  }
}

function bits(n: nat): seq<bool>
{
  if n == 0 then []
  else [if (n % 2 == 0) then false else true] + bits(n/2)
}

function from_bits(s: seq<bool>): nat
  ensures from_bits(s) == from_bits(s, 0)
{
  from_bits(s, 0)
}

function from_bits(s: seq<bool>, acc: nat): nat
  ensures from_bits(s, acc) == acc + from_bits(s)
{
  if s == [] then acc
  else from_bits(s[1..], acc * 2 + (if s[0] then 1 else 0))
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
}

lemma bits_trim_front(n: nat)
  requires n > 0
  ensures from_bits(bits(n)[1..]) == n/2
{}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    return;
  }
  from_bits_append(s[1..], b);
}

lemma from_bits_sum(s1: seq<bool>, s2: seq<bool>)
  ensures from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2)
{
  if s2 == [] {
    return;
  }
  from_bits_sum(s1 + [s2[0]], s2[1..]);
  from_bits_append(s1, s2[0]);
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  ghost var n0 := n;
  var n := n;
  ghost var i: nat := 0;
  bits_from_bits(n);
  while n > 0
    invariant 0 <= n <= n0
    invariant a == exp(b, n0 - n) * c^i
    invariant c == b^i
    invariant i <= n0
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      a := a * c;
      exp_sum(b, n0-n, i);
      n := (n-1) / 2;
      exp_sum_auto(b);
    } else {
      n := n / 2;
    }
    c := c * c;
    exp_sum(b, exp(2, i), exp(2, i));
    i := i + 1;
  }
  return a;
}
