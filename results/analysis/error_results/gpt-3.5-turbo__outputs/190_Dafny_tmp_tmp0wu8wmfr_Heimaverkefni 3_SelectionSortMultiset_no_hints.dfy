
// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{};
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
    min :| min in m;
    var done := multiset{min};
    var m' := m-done;
    while m' != multiset{}
        invariant m == done + m' && min in done && forall z | z in done :: min <= z;
    {
        var z :| z in m';
        done := done+multiset{z};
        m' := m'-multiset{z};
        if z < min { min := z; }
    }
}

// Ekki má breyta þessu falli.
method Test( m: multiset<int> )
{
    var s := Sort(m);
}

method Main()
{
    var m := multiset{0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9};
    var s := Sort(m);
    print s;
}

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{
    s := [];
    var m' := m;
    while m' != multiset{}
        invariant m == m' + multiset(s) && multiset(s) <= m;
        invariant forall x | x in multiset(s) :: x in m;
        invariant forall y | y in m' :: y in m;
    {
        var x := MinOfMultiset(m');
        m' := m' - multiset{x};
        s := s + [x];
    }
    assert multiset(s) == m;
    assert forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    return s;
}