predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l < k < j ==> a[l] <= a[k]
}

method bubbleSorta(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f])
{
  var i := c;
  while i < f
   invariant c <= i <= f
   invariant sorted_seg(a, c, i)
   invariant multiset(a[c..f]) == old(multiset(a[c..f]))
   invariant a[..c] == old(a[..c]) && a[f..] == old(a[f])
   {
    var j := f - 1;

    while j > i
    invariant i <= j < f
    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f])
    {
        assert sorted_seg(a, i, f);
        assert multiset(a[c..f]) == old(multiset(a[c..f]));
        if a[j - 1] > a[j] {
          a[j], a[j - 1] := a[j - 1], a[j];
          
        }
        j := j - 1;
    }
    i := i + 1;
   }
}


method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f])
{
  var i := c;
  var b := true;

  while i < f && b
   invariant c <= i <= f
   invariant sorted_seg(a, c, i)
   invariant multiset(a[c..f]) == old(multiset(a[c..f]))
   invariant a[..c] == old(a[..c]) && a[f..] == old(a[f])
   {
    var j := f - 1;
    
    b := false;

    while j > i
    invariant i <= j < f
    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant multiset(a[c..f]) == old(multiset(a[c..f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f])
    {
        assert sorted_seg(a, i, f);
        assert multiset(a[c..f]) == old(multiset(a[c..f]));
        if a[j - 1] > a[j] {    
          a[j], a[j - 1] := a[j - 1], a[j]; 
          
          b := true;
        }
        j := j - 1;
    }
    i := i + 1;
   }
}