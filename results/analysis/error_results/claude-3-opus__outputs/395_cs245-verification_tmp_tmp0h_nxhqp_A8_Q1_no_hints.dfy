// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;
{
  if n == 0 then 1 else a * power(a, n-1)
}

method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
/*Post-Condition*/ ensures z==power(x,y0);
{
  var y := y0;  //This is here for Dafny's sake and immutable inputs...
  
  /* (| y=y0 ^ y>=0 |)                          - Pre-Condition */
  assert y == y0 && y >= 0;
  /* (| 1=power(x,y0-y) ^ y>=0 |)               - implied (a)   */
  assert 1 == power(x, y0-y) && y >= 0 by {
    assert y0 - y == 0;
    assert power(x, 0) == 1;
  }
  z := 1;
  /* (| z=power(x,y0-y) ^ y>=0 |)               - assignment    */   
  assert z == power(x, y0-y) && y >= 0;
  while (y>0)
  invariant z == power(x, y0-y) && y >= 0
  {
    /*   (| z=power(x,y0-y) ^ y>=0 ^ y>0 |)       - partial-while */  
    assert z == power(x, y0-y) && y >= 0 && y > 0;
    /*   (| z*x=power(x,y0-(y-1)) ^ (y-1)>=0 |)   - implied (b)   */  
    assert z*x == power(x, y0-(y-1)) && (y-1) >= 0 by {
      assert z == power(x, y0-y);
      assert power(x, y0-y) * x == power(x, (y0-y)+1) == power(x, y0-(y-1));
    }
    z := z*x;
    /*   (| z=power(x,y0-(y-1)) ^ (y-1)>=0 |)     - assignment    */        
    assert z == power(x, y0-(y-1)) && (y-1) >= 0;
    y := y-1;
    /*   (| z=power(x,y0-y) ^ y>=0 |)             - assignment    */              
    assert z == power(x, y0-y) && y >= 0;
  }
  /* (| z=power(x,y0-y) ^ y>=0 ^ -(y>0) |)      - partial-while */   
  assert z == power(x, y0-y) && y >= 0 && !(y>0);
  /* (| z=power(x,y0-y) |)                      - implied (c)   */       
  assert z == power(x, y0-y);
  assert y == 0;
  assert y0 - y == y0;
  assert z == power(x, y0-0);
  assert z == power(x, y0);
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/