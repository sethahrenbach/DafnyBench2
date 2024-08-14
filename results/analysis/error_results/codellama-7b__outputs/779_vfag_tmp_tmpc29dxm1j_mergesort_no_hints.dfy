
method ordenar_mergesort(V : array<int>)
  requires V != null
  modifies V
{
  var m : int := V.Length / 2;
  var V1 : array<int> := V[0..m];
  var V2 : array<int> := V[m..V.Length];
  ordenar_mergesort(V1);
  ordenar_mergesort(V2);
  mezclar(V1, V2, V);
}

method mezclar(V1 : array<int>, V2 : array<int>, V : array<int>)
  requires V1 != null && V2 != null && V != null
  modifies V
{
  var i : int := 0;
  var j : int := 0;
  var k : int := 0;
  while i < V1.Length && j < V2.Length && k < V.Length
    invariant i <= V1.Length && j <= V2.Length && k <= V.Length
    invariant V1[0..i] == sorted(V1[0..i]) && V2[0..j] == sorted(V2[0..j])
    invariant V[0..k] == sorted(V[0..k])
  {
    if V1[i] <= V2[j] {
      V[k] := V1[i];
      i := i + 1;
    } else {
      V[k] := V2[j];
      j := j + 1;
    }
    k := k + 1;
  }
  while i < V1.Length && k < V.Length
    invariant i <= V1.Length && k <= V.Length
    invariant V1[0..i] == sorted(V1[0..i])
    invariant V[0..k] == sorted(V[0..k])
  {
    V[k] := V1[i];
    i := i + 1;
    k := k + 1;
  }
  while j < V2.Length && k < V.Length
    invariant j <= V2.Length && k <= V.Length
    invariant V2[0..j] == sorted(V2[0..j])
    invariant V[0..k] == sorted(V[0..k])
  {
    V[k] := V2[j];
    j := j + 1;
    k := k + 1;
  }
}
