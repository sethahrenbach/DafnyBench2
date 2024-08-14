predicate sortedbad(s:string) 
{
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}

method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
{
    b := a;
    var next := 0;
    var white := 0;
    var blue := |b|;
    while (next < blue)
    decreases blue - next
    invariant 0 <= next <= white <= blue <= |b|
    invariant forall k :: 0 <= k < next ==> b[k] == 'b'
    invariant forall k :: next <= k < white ==> b[k] == 'a'
    invariant forall k :: white <= k < blue ==> b[k] != 'b'
    invariant forall k :: blue <= k < |b| ==> b[k] == 'd'
    invariant multiset(b[..]) == multiset(a[..])
    {
        if b[next] == 'b' {
            var tmp := b[next];
            b[next] := b[white];
            b[white] := tmp;
            next := next + 1;
            white := white + 1;
        } else if b[next] == 'a' {
            next := next + 1;
        } else if b[next] == 'd' {
            blue := blue - 1;
            var tmp := b[next];
            b[next] := b[blue];
            b[blue] := tmp;
        }
    }
}

method check() {
    var f:string := "dabdabdab";
    var g:string := BadSort(f);
    assert sortedbad(g);
    assert multiset(f[..]) == multiset(g[..]);
    assert |f| == |g|;
}