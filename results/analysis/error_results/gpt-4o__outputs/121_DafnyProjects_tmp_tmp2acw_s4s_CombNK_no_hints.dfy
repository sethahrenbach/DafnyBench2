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

method combDyn(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  forall i | 0 <= i <= maxj {
       c[i] := 1;
  }
  var i := 1;
  while i <= k 
    invariant 1 <= i <= k + 1
    invariant forall j | 0 <= j <= maxj :: 0 <= k - i + j <= n - i
    invariant forall j | 0 <= j <= maxj :: c[j] == comb(n - i, k - i + j) {:trigger c[j]}
    decreases k - i
  {
    var j := 1;
    while j <= maxj
      invariant 1 <= j <= maxj + 1
      invariant forall j' | 0 <= j' < j :: c[j'] == comb(n - i, k - i + j') {:trigger c[j']}
      invariant j > 0
      decreases maxj - j
    {
      c[j] := c[j] + c[j-1];
      j := j+1;
    } 
    i := i + 1;
  }
  return c[maxj];
}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

method Main()
{
  // Statically checked (proved) test cases!    
  var res1 := combDyn(40, 10);
  print "combDyn(40, 10) = ", res1, "\n";
}

method testComb() {
}