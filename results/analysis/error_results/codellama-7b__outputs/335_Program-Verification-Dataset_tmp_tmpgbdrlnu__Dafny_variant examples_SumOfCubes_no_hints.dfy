
method SumEmUp(n: int, m: int) returns (result: int)
  requires 0 <= n && n <= m;
  ensures 0 <= result && result <= m * m * m;
{
  if m == n then
    result := 0;
  else
    result := n * n * n + SumEmUp(n+1, m);
}

method Socu(n: int, m: int) returns (r: int)
  requires 0 <= n && n <= m;
  ensures r == SumEmUp(n, m);
{
  var a := SocuFromZero(m);
  var b := SocuFromZero(n);
  r := a - b;
  Lemma0(n, m);
}

method SocuFromZero(k: int) returns (r: int)
  requires 0 <= k;
  ensures r == SumEmUp(0, k);
{
  var g := Gauss(k);
  r := g * g;
  Lemma1(k);
}

ghost method Lemma0(n: int, m: int)
  requires 0 <= n && n <= m;
  ensures SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
{
  var k := n;
  while (k < m)
  {
    k := k + 1;
    assert 0 <= k && k <= m;
    assert SumEmUp(0, k) == SumEmUp(0, m) - SumEmUp(0, n);
  }
  Lemma3(0, n);
  Lemma3(n, k);
  Lemma3(0, k);
}

ghost method Lemma1(k: int)
  requires 0 <= k;
  ensures SumEmUp(0, k) == GSum(k) * GSum(k);
{
  var i := 0;
  while (i < k)
  {
    i := i + 1;
    assert 0 <= i && i <= k;
    assert GSum(i) * GSum(i) == SumEmUp(0, k);
  }
  Lemma3(0, k);
}

ghost method Lemma2(k: int)
  requires 0 <= k;
  ensures 2 * GSum(k) == k * (k - 1);
{
  var i := 0;
  while (i < k)
  {
    i := i + 1;
    assert 0 <= i && i <= k;
    assert 2 * GSum(i) == k * (k - 1);
  }
}

ghost method Lemma3(n: int, m: int)
  requires 0 <= n && n <= m;
  ensures SumEmUp(n, m) == SumEmDown(n, m);
{
  var k := n;
  while (k < m)
  {
    k := k + 1;
    assert 0 <= k && k <= m;
    assert SumEmUp(n, m) == SumEmDown(n, m);
  }
}
