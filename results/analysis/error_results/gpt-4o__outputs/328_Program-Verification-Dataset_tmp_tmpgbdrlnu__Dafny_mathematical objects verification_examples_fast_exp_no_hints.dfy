
function exp(b: nat, n: nat): nat {
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
    assert exp(b, n1 + n2) == b * exp(b, (n1-1) + n2);
    assert exp(b, (n1-1) + n2) == exp(b, n1-1) * exp(b, n2);
    assert exp(b, n1 + n2) == b * (exp(b, n1-1) * exp(b, n2));
    assert exp(b, n1 + n2) == (b * exp(b, n1-1)) * exp(b, n2);
    assert exp(b, n1 + n2) == exp(b, n1) * exp(b, n2);
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

function from_bits(s: seq<bool>): nat {
  if s == [] then 0
  else (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
  if n == 0 {
    assert from_bits(bits(0)) == from_bits([]);
    assert from_bits([]) == 0;
    assert 0 == 0;
  } else {
    bits_from_bits(n / 2);
    assert bits(n) == [if n % 2 == 0 then false else true] + bits(n / 2);
    assert from_bits(bits(n)) == (if n % 2 == 0 then 0 else 1) + 2 * from_bits(bits(n / 2));
    assert from_bits(bits(n / 2)) == n / 2;
    assert (if n % 2 == 0 then 0 else 1) + 2 * (n / 2) == n;
  }
}

lemma bits_trim_front(n: nat)
  requires n > 0
  ensures from_bits(bits(n)[1..]) == n/2
{
  bits_from_bits(n);
  assert bits(n) == [if n % 2 == 0 then false else true] + bits(n / 2);
  assert bits(n)[1..] == bits(n / 2);
  assert from_bits(bits(n)[1..]) == from_bits(bits(n / 2));
  assert from_bits(bits(n / 2)) == n / 2;
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    assert from_bits([] + [b]) == from_bits([b]);
    assert from_bits([b]) == (if b then 1 else 0);
    assert from_bits([]) + exp(2, 0) * (if b then 1 else 0) == (if b then 1 else 0);
    assert 0 + 1 * (if b then 1 else 0) == (if b then 1 else 0);
  } else {
    from_bits_append(s[1..], b);
    assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
    assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s[1..]|) * (if b then 1 else 0);
    assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * (from_bits(s[1..]) + exp(2, |s[1..]|) * (if b then 1 else 0));
    assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..]) + 2 * exp(2, |s[1..]|) * (if b then 1 else 0);
    assert from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0);
  }
}

lemma from_bits_sum(s1: seq<bool>, s2: seq<bool>)
  ensures from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2)
{
  if s2 == [] {
    assert from_bits(s1 + []) == from_bits(s1);
    assert from_bits(s1) + exp(2, |s1|) * from_bits([]) == from_bits(s1);
    assert exp(2, |s1|) * 0 == 0;
    assert from_bits(s1) + 0 == from_bits(s1);
  } else {
    from_bits_sum(s1 + [s2[0]], s2[1..]);
    from_bits_append(s1, s2[0]);
    assert from_bits(s1 + s2) == from_bits(s1 + [s2[0]] + s2[1..]);
    assert from_bits(s1 + [s2[0]] + s2[1..]) == from_bits(s1 + [s2[0]]) + exp(2, |s1 + [s2[0]]|) * from_bits(s2[1..]);
    assert from_bits(s1 + [s2[0]]) == from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0);
    assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0) + exp(2, |s1 + [s2[0]]|) * from_bits(s2[1..]);
    assert exp(2, |s1 + [s2[0]]|) == 2 * exp(2, |s1|);
    assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0) + 2 * exp(2, |s1|) * from_bits(s2[1..]);
    assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * ((if s2[0] then 1 else 0) + 2 * from_bits(s2[1..]));
    assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2);
  }
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  ghost var n0 := n;
  var n := n;
  ghost var i: nat := 0;
  bits_from_bits(n0);
  while n > 0
    invariant a * exp(c, n) == exp(b, n0)
    invariant c == exp(b, i)
    invariant n0 == n + from_bits(bits(n0)[..i]) * exp(2, i)
    invariant i <= |bits(n0)|
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      a := a * c;
      exp_sum(b, n0 - n, i);
      n := (n - 1) / 2;
      bits_trim_front(n_loop_top);
      assert from_bits(bits(n_loop_top)[1..]) == n_loop_top / 2;
      assert n == n_loop_top / 2;
    } else {
      n := n / 2;
      bits_trim_front(n_loop_top);
      assert from_bits(bits(n_loop_top)[1..]) == n_loop_top / 2;
      assert n == n_loop_top / 2;
    }
    c := c * c;
    exp_sum(b, i, i);
    i := i + 1;
  }
  return a;
}
