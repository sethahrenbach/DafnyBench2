function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)

method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;

  while (n != 0)
    decreases n
    invariant n >= 0
    invariant a == fusc(N) - fusc(N - n)
    invariant b == fusc(N - n)
  {
    if (n % 2 == 0)
    {
      a := a + b;
      n := n / 2;
    } else {
      b := b + a;
      n := (n - 1) / 2;
    }
  }

  rule1();
  rule2();
}