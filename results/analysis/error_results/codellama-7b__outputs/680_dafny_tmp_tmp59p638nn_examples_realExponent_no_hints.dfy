
ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0
    loop invariant power(n, alpha) > 0.0
    loop variant n
{
    var result: real := 1.0;
    var i: real := 1.0;
    while i <= n
    {
        result := result * alpha;
        i := i + 1.0;
    }
    return result;
}

lemma power_lemma(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) == alpha^n
    assert power(n, alpha) == alpha^n
{
    var result: real := 1.0;
    var i: real := 1.0;
    while i <= n
    {
        result := result * alpha;
        i := i + 1.0;
    }
    assert result == alpha^n;
}

method pow(n: real, alpha: real) returns (result: real)
    requires n > 0.0 && alpha > 0.0
    ensures result == alpha^n
    loop invariant result == alpha^n
    loop variant n
{
    var i: real := 1.0;
    while i <= n
    {
        result := result * alpha;
        i := i + 1.0;
    }
    return result;
}
