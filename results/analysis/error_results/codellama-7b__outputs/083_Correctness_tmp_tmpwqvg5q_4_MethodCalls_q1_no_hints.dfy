
method ComputeFusc(N: int) returns (b: int)
  requires N >= 0
  ensures b == fusc(N)
{
  b := 0;
  var n, a := N, 1;

  while (n != 0)
  {
    ghost var d := n; // termination metric

    // Loop invariant: b == fusc(n)
    assert b == fusc(n);

    // Postcondition: b == fusc(n)
    assert b == fusc(n);

    if (n % 2 == 0)
    {
      // Precondition: n % 2 == 0
      assert n % 2 == 0;

      // Loop invariant: b == fusc(n)
      assert b == fusc(n);

      // Postcondition: b == fusc(n)
      assert b == fusc(n);

      rule4(n/2);
      
      rule3(n/2);
      
      
      a := a + b;
      
      
      n := n / 2;
      
    } else {
      // Precondition: n % 2 == 1
      assert n % 2 == 1;

      // Loop invariant: b == fusc(n)
      assert b == fusc(n);

      // Postcondition: b == fusc(n)
      assert b == fusc(n);

      rule4((n-1)/2);
      
      rule3((n-1)/2);

      
      rule3((n+1)/2);



              b * fusc(n) - b  * fusc(n) + b  * fusc(((n-1)/2)+1) + a * fusc(n);
      
              b * fusc(n) - b  * (fusc(n) - fusc(((n-1)/2)+1)) + a * fusc(n);
      
      
      
      
              a * fusc(n - 1) + b  * fusc(n) - b  * fusc(n-1) + a * fusc(n) - a * fusc(n-1);
 

      
      // Precondition: n % 2 == 1
      assert n % 2 == 1;

      // Loop invariant: b == fusc(n)
      assert b == fusc(n);

      // Postcondition: b == fusc(n)
      assert b == fusc(n);

      b := b + a;
      
      
      n := (n - 1) / 2;

    }
  }

  // Precondition: N >= 0
  assert N >= 0;

  // Postcondition: b == fusc(N)
  assert b == fusc(N);

  rule1();

  rule2();

}
