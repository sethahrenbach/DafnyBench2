
method Busca<T>(a:array<T>, x:T) returns (r:int)
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
  loop invariant 0 <= r ==> r < a.Length && a[r] == x;
  loop invariant r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x;
  loop assigns r;
  loop variant a.Length - r;

  r := 0;
  while r < a.Length
  {
    if a[r] == x
    {
      return r;
    }
    r := r + 1;
  }
  r := -1;
}
