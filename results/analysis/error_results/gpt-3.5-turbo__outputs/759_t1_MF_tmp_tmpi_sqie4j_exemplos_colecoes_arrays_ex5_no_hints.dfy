
method Busca<T>(a:array<T>, x:T) returns (r:int)
  requires a != null
  requires a.Length > 0
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
    var i := 0;
    r := -1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant r < 0 ==> forall j :: 0 <= j < i ==> a[j] != x
      decreases a.Length - i - 1
    {
        if a[i] == x
        {
            r := i;
            return;
        }
        i := i + 1;
    }
}
