// Redo for exam

function gcd(a: nat, b: nat): nat

lemma r1(a: nat)
    ensures gcd(a, 0) == a

lemma r2(a:nat)
    ensures gcd(a, a) == a

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
    decreases a+b, b
{
    if a < b {
        r3(a,b);
        r := GCD1(b, a);
        // Termination:
        // a < b, so (b+a, a) is lexicographically smaller than (a+b, b)
    } else if (a % b == 0) {
        r4(a,b);
        r1(b);
        r := b;
    } else {
        r4(a,b);
        r := GCD1(b, a % b);
        // Termination:
        // a > b > a % b >= 0
        // So (b + a%b, a%b) is lexicographically smaller than (a+b, b)
    }
}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    ensures gcd(a,b) == r
    decreases if b == 0 then a else b, a
{
    r1(a);
    r4(a,b);
    assert ( b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a) )
        &&
        ( (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b))) );
    assert b != 0 || (a > 0 && b >= 0 && gcd(a,b) == a);
    assert b == 0 ==> a > 0 && b >= 0 && gcd(a,b) == a;
    assert (b < 0 || b == 0) || (b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b)));
    assert b >= 0 && b != 0 ==> b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
    if b == 0 {
        r1(a);
        assert gcd(a,b) == a;
        r := a;
        assert gcd(a,b) == r;
    } else {
        r4(a,b);
        // Method call rule
        assert b > 0 && (a % b) >= 0 ==> gcd(a,b) == gcd(b,(a % b));
        var tmp := GCD2(b, a % b);
        // Termination:
        // If b != 0, then (b, a%b) is lexicographically smaller than (b, a)
        // If b == 0, then (a, 0) is lexicographically smaller than (a, b) for any b > 0
        assert gcd(a,b) == tmp;
        r := tmp;
        assert gcd(a,b) == r;
    }
    assert gcd(a,b) == r;
}