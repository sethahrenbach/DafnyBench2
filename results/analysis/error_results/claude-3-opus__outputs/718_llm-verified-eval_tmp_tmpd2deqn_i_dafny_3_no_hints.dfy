function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
    decreases |s| - i
{
    if i+1 < |s| {
        sum_plus(s, i+1);
        assert sum(s, i+1) + s[i+1] == sum(s, i+2);
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    for i := 0 to |ops|
        invariant i <= |ops|
        invariant t == sum(ops, i)
        invariant !result ==> forall n: nat :: n < i ==> sum(ops, n) >= 0
        invariant result ==> exists n: nat :: n <= i && sum(ops, n) < 0
    {
        t := t + ops[i];
        sum_plus(ops, i);
        assert t == sum(ops, i+1);
        if t < 0 {
            result := true;
            assert exists n: nat :: n == i+1 && sum(ops, n) < 0;
            return;
        }
    }
    assert forall n: nat :: n <= |ops| ==> sum(ops, n) >= 0;
    assert !exists n: nat :: n <= |ops| && sum(ops, n) < 0;
}