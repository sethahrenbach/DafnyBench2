
function sum(X_val: array<int>, X_crd: array<nat>, v_val: array<int>, v_crd: array<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat): (s: int)
  reads X_val, X_crd
  requires X_val.Length == X_crd.Length
  requires pX_end <= X_crd.Length
  requires 0 <= kX <= X_crd.Length

  reads v_crd, v_val
  requires v_val.Length == v_crd.Length
  requires pV_end <= v_crd.Length
  requires 0 <= kV <= v_crd.Length

  loop invariant 0 <= kX <= X_crd.Length
  loop invariant 0 <= kV <= v_crd.Length
  loop assigns kX, kV

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
  ensures s == sum(X_val, X_crd, v_val, v_crd, 0, v_crd.Length, pX_end, pV_end)
