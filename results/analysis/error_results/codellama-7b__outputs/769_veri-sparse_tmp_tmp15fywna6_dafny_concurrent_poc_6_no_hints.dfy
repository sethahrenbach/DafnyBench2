
method foo(n: nat) returns (m: nat)
    ensures m == n + 1
    decreases n
{
    if n == 0 {
        m := 1;
    } else {
        m := foo(n - 1) + 1;
    }
}
