predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0;
    assert positive(v[..0]);
    while i<v.Length && v[i]>=0
        decreases v.Length - i
        invariant 0 <= i <= v.Length
        invariant positive(v[..i])
    {
        i:=i+1;
    }
    assert i==v.Length ==> positive(v[..v.Length]);
    b := i==v.Length;
}

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0; b:=true;
    while(i<v.Length && b)
        decreases v.Length - i
        invariant 0 <= i <= v.Length
        invariant b ==> positive(v[..i])
    {
        b:=v[i]>=0;
        i:=i+1;
    }
    assert b ==> positive(v[..v.Length]);
}

method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=0; b:=true;
    while(i<v.Length && b)
        decreases v.Length - i
        invariant 0 <= i <= v.Length
        invariant b ==> positive(v[..i])
    {
        b:=v[i]>=0;
        i:=i+1;
    }
    assert b ==> positive(v[..v.Length]);
}

method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    var i:=v.Length-1;
    while(i>=0 && v[i]>=0)
        decreases i + 1
        invariant -1 <= i < v.Length
        invariant forall k :: i < k < v.Length ==> v[k] >= 0
    {
        i:=i-1;
    }
    b:= i==-1;
    assert b ==> positive(v[..v.Length]);
}