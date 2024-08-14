function sum(s: seq<int>, n: nat): int
    requires n <= |s|
    ensures n == 0 ==> sum(s, n) == 0
    ensures n > 0 ==> sum(s, n) == s[0] + sum(s[1..], n-1)
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
    if i == 0 {
        assert sum(s, 0) == 0;
        assert sum(s, 1) == s[0];
    } else {
        assert sum(s, i) == s[0] + sum(s[1..], i-1);
        assert sum(s, i+1) == s[0] + sum(s[1..], i);
        sum_plus(s[1..], i-1);
        assert sum(s[1..], i-1) + s[i] == sum(s[1..], i);
        assert s[0] + (sum(s[1..], i-1) + s[i]) == s[0] + sum(s[1..], i);
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    for i := 0 to |ops|
        invariant 0 <= i <= |ops|
        invariant t == sum(ops[..i], i)
        invariant result <==> exists n: nat :: n <= i && sum(ops, n) < 0
    {
        if i < |ops| {
            t := t + ops[i];
            if t < 0 {
                result := true;
                return;
            }
        }
    }
    assert !result ==> forall n: nat :: n <= |ops| ==> sum(ops, n) >= 0;
}