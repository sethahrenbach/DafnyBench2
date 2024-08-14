/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}
by method
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  var i := 0;
  while i <= maxj
    invariant 0 <= i <= maxj+1
    invariant forall j | 0 <= j < i :: c[j] == 1
  {
    c[i] := 1;
    i := i + 1;
  }
  i := 1;
  while i <= k
    invariant 1 <= i <= k+1
    invariant forall j | 0 <= j <= maxj :: c[j] == comb(i+j-1, j)
  {
    var j := 1;
    while j <= maxj
      invariant 1 <= j <= maxj+1
      invariant forall jj | 0 <= jj < j :: c[jj] == comb(i+jj, jj)
      invariant forall jj | j <= jj <= maxj :: c[jj] == comb(i-1+jj, jj)
    {
      c[j] := c[j] + c[j-1];
      j := j+1;
    }
    i := i + 1; 
  }
  assert forall j | 0 <= j <= maxj :: c[j] == comb(k+j, j);
  assert c[maxj] == comb(n, k);
  return c[maxj];
}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{
  if k == 0 {
    assert comb(n, k) == 1 == comb(n, n-k);
  } else if k == n {
    assert comb(n, k) == 1 == comb(n, n-k);
  } else {
    calc == {
      comb(n, k);
      comb(n-1, k) + comb(n-1, k-1);
      { combProps(n-1, k); }
      comb(n-1, n-1-k) + comb(n-1, k-1);
      comb(n-1, n-k-1) + comb(n-1, k-1);
      { assert n-k-1 == (n-1)-(k-1); }
      comb(n-1, (n-1)-(k-1)) + comb(n-1, k-1);
      { combProps(n-1, k-1); }
      comb(n-1, k-1) + comb(n-1, (n-1)-(k-1));
      comb(n, n-k);
    }
  }
}

method Main()
{
  // Statically checked (proved) test cases!    
  var res1 := comb(40, 10);
  print "combDyn(40, 10) = ", res1, "\n";
}

method testComb() {
  // Test cases
  assert comb(0, 0) == 1;
  assert comb(1, 0) == 1;
  assert comb(1, 1) == 1;
  assert comb(2, 0) == 1;
  assert comb(2, 1) == 2;
  assert comb(2, 2) == 1;
  assert comb(5, 2) == 10;
  assert comb(5, 3) == 10;
  assert comb(6, 3) == 20;
}