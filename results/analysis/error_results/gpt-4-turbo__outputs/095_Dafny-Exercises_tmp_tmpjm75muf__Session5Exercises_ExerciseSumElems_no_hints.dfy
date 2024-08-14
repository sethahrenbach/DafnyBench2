
function SumR(s: seq<int>): int
{
    if (s == []) then 0
    else SumR(s[..|s|-1]) + s[|s|-1]
}

function SumL(s: seq<int>): int
{
    if (s == []) then 0
    else s[0] + SumL(s[1..])
}

lemma concatLast(s: seq<int>, t: seq<int>)
    requires t != []
    ensures (s + t)[..|s + t| - 1] == s + (t[..|t| - 1])
{}

lemma concatFirst(s: seq<int>, t: seq<int>)
    requires s != []
    ensures (s + t)[1..] == s[1..] + t
{}

lemma {:induction s, t} SumByPartsR(s: seq<int>, t: seq<int>)
    ensures SumR(s + t) == SumR(s) + SumR(t)
{
    if (t == []) {
        assert SumR(s + t) == SumR(s);
    } else if (s == []) {
        assert SumR(s + t) == SumR(t);
    } else {
        concatLast(s, t);
        SumByPartsR(s, t[..|t|-1]);
        assert SumR(s + t) == SumR(s) + SumR(t[..|t|-1]) + t[|t|-1];
    }
}

lemma {:induction s, t} SumByPartsL(s: seq<int>, t: seq<int>)
    ensures SumL(s + t) == SumL(s) + SumL(t)
{
    if (t == []) {
        assert SumL(s + t) == SumL(s);
    } else if (s == []) {
        assert SumL(s + t) == SumL(t);
    } else {
        concatFirst(s, t);
        SumByPartsL(s[1..], t);
        assert SumL(s + t) == s[0] + SumL(s[1..] + t);
    }
}

lemma {:induction s, i, j} equalSumR(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    ensures SumR(s[i..j]) == SumL(s[i..j])
{
    if (i == j) {
        assert SumR(s[i..j]) == 0;
        assert SumL(s[i..j]) == 0;
    } else if (s == []) {
        assert SumR(s[i..j]) == 0;
        assert SumL(s[i..j]) == 0;
    } else {
        equalSumR(s, i, j - 1);
        assert SumR(s[i..j]) == SumR(s[i..j - 1]) + s[j - 1];
        assert SumL(s[i..j]) == SumL(s[i..j - 1]) + s[j - 1];
    }
}

lemma equalSumsV() 
    ensures forall v: array<int>, i, j | 0 <= i <= j <= v.Length :: SumR(v[i..j]) == SumL(v[i..j])
{
    forall v: array<int>, i, j | 0 <= i <= j <= v.Length
        ensures SumR(v[i..j]) == SumL(v[i..j])
    {
        equalSumR(v[..], i, j);
    }
}

function SumV(v: array<int>, c: int, f: int): int
    requires 0 <= c <= f <= v.Length
    reads v
{
    SumR(v[c..f])
}

lemma ArrayFacts<T>()
    ensures forall v: array<T> :: v[..v.Length] == v[..]
    ensures forall v: array<T> :: v[0..] == v[..]
    ensures forall v: array<T> :: v[0..v.Length] == v[..]
    ensures forall v: array<T> :: |v[0..v.Length]| == v.Length
    ensures forall v: array<T> | v.Length >= 1 :: |v[1..v.Length]| == v.Length - 1
    ensures forall v: array<T> :: forall k: nat | k < v.Length :: v[..k + 1][..k] == v[..k]
{
    equalSumsV();
}

method sumElems(v: array<int>) returns (sum: int)
    ensures sum == SumR(v[..])
{
    ArrayFacts<int>();
    sum := 0;
    var i := 0;
    while (i < v.Length)
        invariant 0 <= i <= v.Length
        invariant sum == SumR(v[..i])
    {
        sum := sum + v[i];
        i := i + 1;
    }
}

method sumElemsB(v: array<int>) returns (sum: int)
    ensures sum == SumR(v[0..v.Length])
{
    ArrayFacts<int>();
    sum := 0;
    var i := v.Length;
    equalSumsV();
    while (i > 0)
        invariant 0 <= i <= v.Length
        invariant sum == SumR(v[i..v.Length])
    {
        sum := sum + v[i - 1];
        i := i - 1;
    }
}