
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
  forall i | 0 <= i <= maxj {
       c[i] := 1;
  }
  var i := 1;
  while i <= k 
    invariant 1 <= i <= k+1
    invariant forall j | 0 <= j <= maxj :: c[j] == comb(i-1, j)
  {
    var j := 1;
    while j <= maxj
      invariant 1 <= j <= maxj+1
      invariant forall l | 0 <= l < j :: c[l] == comb(i, l)
      invariant c[0] == 1
      invariant forall l | 1 <= l <= j :: c[l] == comb(i-1, l)
      invariant c[j-1] == comb(i-1, j-1)
    {
      c[j] := c[j] + c[j-1];
      j := j+1;
    } 
    i := i + 1;
  }
  assert c[maxj] == comb(n, k);
  return c[maxj];
}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

method Main()
{
  // Statically checked (proved) test cases!    

  var res1 := comb(40, 10);
  print "combDyn(40, 10) = ", res1, "\n";

}

method testComb() {
}
