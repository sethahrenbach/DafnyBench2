function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    assert exp(b, n1 + n2) == exp(b, n2);
    assert exp(b, n1) == 1;
    assert exp(b, n1) * exp(b, n2) == exp(b, n2);
  } else {
    exp_sum(b, n1-1, n2);
    assert exp(b, (n1-1) + n2) == exp(b, n1-1) * exp(b, n2);
    assert exp(b, n1 + n2) == b * exp(b, (n1-1) + n2);
    assert exp(b, n1) == b * exp(b, n1-1);
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
  if n != 0 {
    bits_from_bits(n/2);
    assert from_bits(bits(n/2)) == n/2;
    assert bits(n) == [if (n % 2 == 0) then false else true] + bits(n/2);
    assert from_bits(bits(n)) == (if (n % 2 == 0) then 0 else 1) + 2 * from_bits(bits(n/2));
    assert from_bits(bits(n)) == (if (n % 2 == 0) then 0 else 1) + 2 * (n/2);
    assert from_bits(bits(n)) == n;
  }
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s != [] {
    from_bits_append(s[1..], b);
    assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0);
    exp_sum(2, |s|-1, 1);
    assert exp(2, |s|) == exp(2, |s|-1) * 2;
    assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
    assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * (from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0));
    assert from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0);
  }
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  var n := n;
  ghost var n0 := n;
  ghost var i: nat := 0;
  
  bits_from_bits(n);
  
  while n > 0
    invariant 0 <= n <= n0
    invariant a == exp(b, n0-n)
    invariant c == exp(b, exp(2, i))
    invariant n == from_bits(bits(n0)[i..])
    invariant i == |bits(n0)| - |bits(n)|
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      a := a * c;
      exp_sum(b, n0-n, exp(2, i));
      assert a == exp(b, n0-n+exp(2, i));
      n := n / 2;
      assert n == from_bits(bits(n_loop_top)[1..]);
      assert n0 - n == n0 - n_loop_top + exp(2, i);
      exp_sum_auto(b);
      assert a == exp(b, n0 - n);
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      assert n == from_bits(bits(n0)[i+1..]);
    } else {
      n := n / 2;
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      assert n == from_bits(bits(n0)[i+1..]);
    }
    c := c * c;
    exp_sum(b, exp(2, i), exp(2, i));
    assert c == exp(b, exp(2, i+1));
    i := i + 1;
  }
  assert n == 0;
  assert bits(n0)[i..] == [];
  assert from_bits(bits(n0)[i..]) == from_bits([]);
  assert from_bits([]) == 0;
  assert i == |bits(n0)|;
  assert n0 - n == n0;
  assert a == exp(b, n0 - n);
  assert a == exp(b, n0);
  return a;
}