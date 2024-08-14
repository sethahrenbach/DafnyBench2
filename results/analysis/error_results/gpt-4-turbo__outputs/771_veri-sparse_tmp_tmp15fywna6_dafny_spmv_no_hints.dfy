
function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  reads X_val, X_crd, v
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  decreases k - b
{
  if k <= b then 
    0
  else  
    sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
}

method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
{
  var N := X_pos.Length - 1;
  y := new int[N];
  var n := 0;
  while n < N
    invariant 0 <= n <= N
    invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {
    var sum_k := 0;
    var k := X_pos[n];
    while k < X_pos[n + 1]
      invariant k <= X_pos[n + 1]
      invariant sum_k == sum(X_val, X_crd, v, X_pos[n], k)
    {
      sum_k := sum_k + X_val[k] * v[X_crd[k]];
      k := k + 1;
    }
    y[n] := sum_k;
    n := n + 1;
  }
}

method Main() {
  var X_val := new int[4](i => 1);
  var X_crd := new nat[4](i => if i <= 3 then (3 - i) * 2 else 0);
  var X_pos := new nat[9];
  X_pos[0] := 0;
  X_pos[1] := 1;
  X_pos[2] := 1;
  X_pos[3] := 2;
  X_pos[4] := 2;
  X_pos[5] := 3;
  X_pos[6] := 3;
  X_pos[7] := 4;
  X_pos[8] := 4;

  var v := new int[8];
  v[0] := 30;
  v[1] := 0;
  v[2] := 31;
  v[3] := 0;
  v[4] := 32;
  v[5] := 0;
  v[6] := 33;
  v[7] := 0;

  var y := SpMV(X_val, X_crd, X_pos, v);

  var i := 0;
  while i < y.Length { print y[i]; print "; "; i := i + 1; }
}
