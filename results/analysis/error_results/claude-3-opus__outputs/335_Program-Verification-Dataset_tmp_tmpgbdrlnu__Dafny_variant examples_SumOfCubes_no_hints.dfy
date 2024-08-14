// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class SumOfCubes {
  static function SumEmUp(n: int, m: int): int
    requires 0 <= n && n <= m;
    decreases m - n;
  {
    if m == n then 0 else n*n*n + SumEmUp(n+1, m)
  }

  static method Socu(n: int, m: int) returns (r: int)
    requires 0 <= n && n <= m;
    ensures r == SumEmUp(n, m);
  {
    var a := SocuFromZero(m);
    var b := SocuFromZero(n);
    r := a - b;
    Lemma0(n, m);
  }

  static method SocuFromZero(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == SumEmUp(0, k);
  {
    var g := Gauss(k);
    r := g * g;
    Lemma1(k);
  }

  ghost static method Lemma0(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmUp(0, m) - SumEmUp(0, n);
  {
    var k := n;
    while (k < m) 
      invariant n <= k <= m;
      invariant SumEmUp(n, k) == SumEmUp(0, k) - SumEmUp(0, n);
    {
      Lemma3(n, k);
      Lemma3(0, k);
      Lemma3(0, k+1);
      calc == {
        SumEmUp(n, k+1);
        SumEmUp(n, k) + (k*k*k);
        { Lemma3(n, k); }
        SumEmUp(0, k) - SumEmUp(0, n) + (k*k*k);
        { Lemma3(0, k); Lemma3(0, k+1); }
        SumEmUp(0, k+1) - SumEmUp(0, n);
      }
      k := k + 1;
    }
    Lemma3(0, n);
    Lemma3(n, k);
    Lemma3(0, k);
  }

  static function GSum(k: int): int
    requires 0 <= k;
    decreases k;
  {
    if k == 0 then 0 else GSum(k-1) + k-1
  }

  static method Gauss(k: int) returns (r: int)
    requires 0 <= k;
    ensures r == GSum(k);
  {
    r := k * (k - 1) / 2;
    Lemma2(k);
  }

  ghost static method Lemma1(k: int)
    requires 0 <= k;
    ensures SumEmUp(0, k) == GSum(k) * GSum(k);
  {
    var i := 0;
    while (i < k)
      invariant 0 <= i <= k;
      invariant SumEmUp(0, i) == GSum(i) * GSum(i);
    {
      Lemma3(0, i);
      Lemma2(i);
      Lemma2(i+1);
      calc == {
        SumEmUp(0, i+1);
        SumEmUp(0, i) + (i*i*i);
        { Lemma3(0, i); }
        GSum(i) * GSum(i) + (i*i*i);
        GSum(i) * GSum(i) + (GSum(i+1) - GSum(i)) * (GSum(i+1) + GSum(i));
        GSum(i+1) * GSum(i+1);
      }
      i := i + 1;
    }
    Lemma3(0, k);
  }

  ghost static method Lemma2(k: int)
    requires 0 <= k;
    ensures 2 * GSum(k) == k * (k - 1);
  {
    var i := 0;
    while (i < k)
      invariant 0 <= i <= k;
      invariant 2 * GSum(i) == i * (i - 1);
    {
      calc == {
        2 * GSum(i+1);
        2 * (GSum(i) + i);
        { Lemma2(i); }
        i * (i - 1) + 2*i;
        i*i + i;
        (i+1) * i;
      }
      i := i + 1;
    }
  }

  static function SumEmDown(n: int, m: int): int
    requires 0 <= n && n <= m;
    decreases m - n;
  {
    if m == n then 0 else SumEmDown(n, m-1) + (m-1)*(m-1)*(m-1)
  }

  ghost static method Lemma3(n: int, m: int)
    requires 0 <= n && n <= m;
    ensures SumEmUp(n, m) == SumEmDown(n, m);
  {
    var k := n;
    while (k < m)
      invariant n <= k <= m;
      invariant SumEmUp(n, k) == SumEmDown(n, k);
    {
      calc == {
        SumEmUp(n, k+1);
        SumEmUp(n, k) + (k*k*k);
        { Lemma3(n, k); }
        SumEmDown(n, k) + (k*k*k);
        SumEmDown(n, k+1);
      }
      k := k + 1;
    }
  }
}