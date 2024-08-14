
method BadSort(a: string) returns (b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  ensures sortedbad(b)
  ensures multiset(b[..]) == multiset(a[..])
{
  b := a;
  var next:int := 0;
  var aPointer:int := 0;
  var dPointer:int := |b|;

  while (next != dPointer)
  {
    // loop invariant: b[0..next] is sorted
    // loop invariant: b[next..aPointer] contains only 'a' and 'b'
    // loop invariant: b[aPointer..dPointer] contains only 'd'
    // loop invariant: b[dPointer..|b|] is sorted
    assert sortedbad(b[0..next]);
    assert multiset(b[next..aPointer]) == multiset({'a', 'b'});
    assert multiset(b[aPointer..dPointer]) == multiset({'d'});
    assert sortedbad(b[dPointer..|b|]);

    if(b[next] == 'a'){
      next := next + 1;
    } 
    
    else if(b[next] == 'b'){
      b := b[next := b[aPointer]][aPointer := b[next]];
      next := next + 1;
      aPointer := aPointer + 1;
    }
      
    else{
      dPointer := dPointer - 1;
      b := b[next := b[dPointer]][dPointer := b[next]];
    } 
  } 
}

function sortedbad(s: string): bool
  requires forall i :: 0 <= i < |s| ==> s[i] in {'b', 'a', 'd'}
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
  return true;
}
