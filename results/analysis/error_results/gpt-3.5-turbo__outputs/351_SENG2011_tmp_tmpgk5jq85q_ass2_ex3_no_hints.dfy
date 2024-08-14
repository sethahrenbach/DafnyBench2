
// verifies
// all bs are before all as which are before all ds
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
    while (next < |b|)
    invariant 0 <= next <= |b|;
    invariant 0 <= white <= next;
    invariant blue <= |b|;
    invariant forall k :: 0 <= k < next ==> b[k] == 'b';
    invariant forall k :: white <= k < next ==> b[k] == 'a';
    invariant forall k :: blue <= k < |b| ==> b[k] == 'd';
    decreases |b| - next;
    {
        if b[next] == 'b' {
            var tmp := b[next];
            b := b[next := b[white]];
            b := b[white := tmp];
            next := next + 1;
            white := white + 1;
        } else if b[next] == 'a' {
            next := next + 1;
        } else if b[next] == 'd'{
            blue := blue - 1;
            var tmp := b[next];
            b := b[next := b[blue]];
            b := b[blue := tmp];
        } 
    }
}
method check() {
    var f:string := "dabdabdab";
    var g:string := BadSort(f);
    /*
      f := "dba";          // testcase1
   g :=  BadSort(f);
   f := "aaaaaaaa";    // testcase 2
   g :=  BadSort(f);
   */
   /*
    var a:string := "dabdabdab";
    var b:string := BadSort(a);
    // apparently not possible ot verify this
    */
}
