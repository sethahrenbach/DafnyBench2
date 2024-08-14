
method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
  requires a.Length > 0
  requires 0 <= s < a.Length
  requires e <= a.Length
  requires e > s
  ensures min_i >= s 
  ensures min_i < e 
  ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
    min_i := s;
    var i : int := s + 1;  

    while i < e 
      invariant s <= i <= e
      invariant s <= min_i < e
      invariant forall k: int :: s <= k < i ==> a[min_i] <= a[k]
    {
        if a[i] < a[min_i] {
            min_i := i;
        }
        i := i + 1;
    }
}

predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

method selection_sort(ns: array<int>) 
  requires ns.Length >= 0
  ensures is_sorted(ns[..])
  ensures is_permutation2(old(ns[..]), ns[..])
  modifies ns
{
    var i: int := 0;
    var l: int := ns.Length;
    while i < l
      invariant 0 <= i <= l
      invariant is_sorted(ns[..i])
      invariant is_permutation2(old(ns[..]), ns[..])
      invariant forall j: int :: i <= j < l ==> exists k: int :: i <= k < l && ns[j] == old(ns[k])
      invariant forall k: int :: i <= k < l ==> exists j: int :: i <= j < l && ns[k] == old(ns[j])
    {
        var min_i: int := find_min_index(ns, i, l);
        var temp := ns[i];
        ns[i] := ns[min_i];
        ns[min_i] := temp;
        i := i + 1;
    }
}
