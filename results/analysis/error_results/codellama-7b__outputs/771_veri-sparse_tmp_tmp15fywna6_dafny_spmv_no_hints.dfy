
method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v: array<int>): (y: array<int>)
  requires X_crd.Length >= 1
  requires X_crd.Length == X_val.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
{
  var N: nat := X_pos.Length - 1;
  y := new int[N](i => 0);
  var n: nat := 0;
  while n < N
    { 
      var k: nat := X_pos[n];
      while k < X_pos[n + 1]
        {
          y[n] := y[n] + X_val[k] * v[X_crd[k]];
          k := k + 1;
        }
      n := n + 1;
    }
}
