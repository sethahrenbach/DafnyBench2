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
    return;
  }
  bits_from_bits(n / 2);
  assert from_bits(bits(n)) == (if n % 2 == 1 then 1 else 0) + 2 * from_bits(bits(n / 2));
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  var m := n; // Corrected mutable variable for the loop
  ghost var originalN := n; // Ghost variable to hold the original value of n for the invariant
  ghost var i: nat := 0; // Counter for the power of 2
  while m > 0
    invariant a * exp(c, 2^i) == exp(b, originalN - m)
    invariant c == exp(b, 2^i)
  {
    if m % 2 == 1 {
      a := a * c;
    }
    c := c * c;
    m := m / 2;
    i := i + 1;
  }
  return a;
}