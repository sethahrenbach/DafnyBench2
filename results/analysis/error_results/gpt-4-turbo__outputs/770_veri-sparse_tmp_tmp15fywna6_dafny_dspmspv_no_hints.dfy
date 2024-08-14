
function sum(X_val : array<int>, X_crd : array<nat>,
             v_val : array<int>, v_crd : array<nat>, kX : nat, kV : nat, pX_end : nat, pV_end : nat) : int 
  reads X_val, X_crd, v_val, v_crd
  requires X_val.Length == X_crd.Length
  requires pX_end <= X_crd.Length
  requires 0 <= kX <= X_crd.Length
  requires v_val.Length == v_crd.Length
  requires pV_end <= v_crd.Length
  requires 0 <= kV <= v_crd.Length
  decreases pX_end - kX, pV_end - kV
{
  if pV_end <= kV || pX_end <= kX then 
    0
  else if X_crd[kX] == v_crd[kV] then 
    sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
  else if X_crd[kX] < v_crd[kV] then 
    sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
  else 
    sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
}

method DSpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
               X_crd1 : array<nat>, X_len: nat,
               v_val : array<int>, v_crd : array<nat>) returns (y : array<int>)
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length
  requires X_len >= X_crd1.Length
  requires forall i :: 0 <= i < X_crd1.Length ==> X_crd1[i] < X_len
  requires X_crd1.Length < X_pos.Length
  requires forall i, j :: 0 <= i < j < X_crd1.Length ==> X_crd1[i] < X_crd1[j]
  requires v_val.Length == v_crd.Length
  ensures y.Length == X_len
  ensures forall i :: 0 <= i < y.Length ==> 
    y[i] == 
      if exists j :: 0 <= j < X_crd1.Length && X_crd1[j] == i then 
        sum(X_val, X_crd, v_val, v_crd, X_pos[index(X_crd1, i)], 0, X_pos[index(X_crd1, i) + 1], v_val.Length)
      else 0
{
  y := new int[X_len](i => 0);
  for n := 0 to X_crd1.Length - 1 {
    var kX := X_pos[n];
    var pX_end := X_pos[n + 1];
    var kV := 0;
    var pV_end := v_val.Length;
    while kX < pX_end && kV < pV_end {
      if X_crd[kX] == v_crd[kV] {
        y[X_crd1[n]] := y[X_crd1[n]] + X_val[kX] * v_val[kV];
        kX := kX + 1;
        kV := kV + 1;
      } else if X_crd[kX] < v_crd[kV] {
        kX := kX + 1;
      } else {
        kV := kV + 1;
      }
    }
  }
}
