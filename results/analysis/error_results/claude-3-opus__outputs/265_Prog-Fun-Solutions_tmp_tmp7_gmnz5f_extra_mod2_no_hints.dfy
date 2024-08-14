ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{
    // Invariant: x = 5^(log_3 n - log_3 k) and y = f2(n) - x*f2(k)
    // Variant: k
    var x:nat := 1;
    var y:nat := 0;
    var k:nat := n;
    while k > 0
        invariant x == power(5, log(n,3) - log(k,3))
        invariant y == f2(n) - x*f2(k)
        decreases k
    {
        var m := k%4;
        y := x*m + y;
        calc == {
            y;
            x*m + y;
            x*m + f2(n) - x*f2(k);
            {
                assert f2(k) == 5*f2(k/3) + m; // Property of f2
            }
            x*m + f2(n) - x*(5*f2(k/3) + m);
            f2(n) - x*5*f2(k/3);
        }
        x := 5*x;
        k := k/3;
    }
    assert k == 0;
    assert log(k,3) == 0 by {
        log_base_zero(3, k);
    }
    assert x == power(5, log(n,3)) by {
        assert log(k,3) == 0;
        log_mul_lemma(3, n, 1);
        assert log(n,3) == log(n,3) + log(k,3);
    }
    assert f2(k) == 0;
    assert y == f2(n) - x*f2(k) == f2(n) - x*0 == f2(n);
    a := y;
}

// Helper lemmas
lemma {:induction n} log_base_zero(b:nat, n:nat)
    requires 1 < b
    ensures n < b ==> log(n, b) == 0
{
}

lemma {:induction n} log_mul_lemma(b:nat, n:nat, m:nat)
    requires b > 1
    ensures log(n*m, b) == log(n, b) + log(m, b)
{
}

lemma {:induction n} power_log_lemma(b:nat, n:nat)
    requires 1 < b
    ensures power(b, log(n, b)) <= n < b * power(b, log(n, b))
{
}

function log(n:nat, b:nat):nat 
    requires 1 < b
{
    if n < b then 0 else 1 + log(n / b, b)
}

function power(b:nat, e:nat):nat
    decreases e
{
    if e == 0 then 1 else b * power(b, e - 1)
}