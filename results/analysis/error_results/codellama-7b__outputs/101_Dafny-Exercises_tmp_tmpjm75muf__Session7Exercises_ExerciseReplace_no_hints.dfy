
method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{
    var i:=0;
    loopInvariant(0<=i<v.Length)
    loopInvariant(forall k::0<=k<i ==> v[k]==old(v[k]))
    loopInvariant(forall k::i<=k<v.Length ==> v[k]==old(v[k]) || v[k]==y)
    while(i<v.Length)
    {
        assert(v[i]==x ==> v[i]==y);
        assert(v[i]!=x ==> v[i]==old(v[i]));
        if(v[i]==x){
            v[i]:=y;
        }
        i:=i+1;
    }
}
