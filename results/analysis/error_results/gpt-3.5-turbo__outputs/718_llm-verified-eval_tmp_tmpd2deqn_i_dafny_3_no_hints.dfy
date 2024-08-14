function sum(s: seq<int>, n: nat) returns (res: int)
    requires n <= |s|
{
    if |s| == 0 || n == 0 {
        res := 0;
    } else {
        res := s[0] + sum(s[1..], n-1);
    }
}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
    if |s| == 0 || i == 0 {
        assert sum(s, i) + s[i] == sum(s, i+1);
    } else {
        assert sum(s, i) + s[i] == s[0] + sum(s[1..], i-1) + s[i];
        sum_plus(s, i-1);
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    var i := 0;
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant t == sum(ops, i)
        invariant result <==> exists n: nat :: n <= i && sum(ops, n) < 0
    {
        t := t + ops[i];
        sum_plus(ops, i);
        if t < 0 {
            result := true;
            return;
        }
        i := i + 1;
    }
}