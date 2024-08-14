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
{
    if (i < |s|) {
        assert sum(s, i) + s[i] == s[i] + sum(s[1..], i); // Unfold sum at i
        assert sum(s, i+1) == s[i] + sum(s[1..], i); // Unfold sum at i+1
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    var n := |ops|;
    if n == 0 {
        return; // No elements to process
    }
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant t == sum(ops, i)
    {
        t := t + ops[i];
        if t < 0 {
            result := true;
            break;
        }
    }
    // Ensure the loop invariant holds at the end of the loop
    if n > 0 && !result {
        assert t == sum(ops, n);
    }
}