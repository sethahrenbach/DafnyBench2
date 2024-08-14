/*
Dafny include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program

method SqrSum(n: int) returns (s: int)
  requires n >= 0
  ensures s == SqrSumRec(n)
{
  var i,k : int;
  s := 0;
  k := 1;
  i := 1;
  while (i <= n) 
    invariant 1 <= i <= n+1
    invariant s == SqrSumRec(i-1)
    invariant k == i*i
  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i+1;
  }
}

method DivMod(a: int, b: int) returns (q: int, r: int)
  requires b > 0 && a >= 0
  ensures a == b*q + r && 0 <= r < b
{
  q := 0;
  r := a;
  while (r >= b)
    invariant a == b*q + r && r >= 0
    decreases r
  {
    r := r - b;
    q := q + 1;
  }
}

/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert
method HoareTripleAssmAssrt()
{
  var i: int := *;
  var k: int := *;
  // (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
  assume k == i*i;   // P = precondition
  k := k + 2 * i + 1;  // S
  assert k == (i+1)*(i+1);  // Q = postcondition
}

// varianta requires-ensures

method HoareTripleReqEns(i: int, k: int) returns (k': int)
  // (| k == i*i |) k := k + 2 * i +1; (| k = (i+1)*(i+1) |)
  requires  k == i*i
  ensures  k' == (i+1)*(i+1)
{
  k' := k + 2 * i + 1;
}

/*
regula pentru while
*/

// varianta cu invariant
method Invariant1()
{
  // var n: int := *;  // havoc
  var n: int :| n >= 0;  
  var y := n;
  var x := 0;
  while (y >= 0)
    invariant x + y == n
    decreases y
  {
    x := x+1;
    y := y-1;
  }
  //assert x == n && y == -1;
}

//specificarea sumei de patrate
function SqrSumRec(n: int) : int
  requires n >= 0
{
  if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

// verificarea programului pentru suma de patrate

method SqrSum1(n: int) returns (s: int)
  requires n >= 0
  ensures s == SqrSumRec(n)
{
  var i,k : int;
  s := 0;
  k := 1;
  i := 1;
  while (i <= n)
    invariant 1 <= i <= n+1
    invariant s == SqrSumRec(i-1)
    invariant k == i*i
  {
    s := s + k;
    k := k + 2 * i + 1;
    i := i+1;
  }
}

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
lemma L1(n: int)
  requires n >= 0
  ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
  if n == 0 {
    //assert SqrSumRec(0) == 0 == 0*(0+1)*(2*0+1)/6;
  } else {
    L1(n-1);
    calc == {
      SqrSumRec(n);
      n*n + SqrSumRec(n-1);
      n*n + (n-1)*n*(2*n-1)/6;
      6*n*n + (n-1)*n*(2*n-1);
      6*n*n + n*(2*n*n-3*n+1);
      n*(6*n + 2*n*n-3*n+1);
      n*(2*n*n+3*n+1);
      n*((2*n+1)*n + (2*n+1));
      n*(2*n+1)*(n+1);
      n*(n+1)*(2*n+1);
      n*(n+1)*(2*n+1)/6;
    }
  }
}

method DivMod1(a: int, b: int) returns (q: int, r: int)
  requires b > 0 && a >= 0
  ensures a == b*q + r && 0 <= r < b
{
  q := 0;
  r := a;
  while (r >= b)
    invariant a == b*q + r && r >= 0
    decreases r
  {
    r := r - b;
    q := q + 1;
  }
}

method Main()
{
  var v := SqrSum(5);
  print "SqrSum(5): ", v, "\n";

  var q, r := DivMod(5, 3);
  print "DivMod(5, 3): ", q, ", ", r, "\n";
}