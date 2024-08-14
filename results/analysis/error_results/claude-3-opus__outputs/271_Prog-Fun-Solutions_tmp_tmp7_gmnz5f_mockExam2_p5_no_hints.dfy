// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    // Initialize variables
    var a := 1;
    var b := 0;
    var k := n;

    // Loop invariant:
    // - a == 3^((n-k)/5)
    // - b == f(k) - a*k
    // - 0 <= k <= n
    while k >= 5
        invariant a == power(3, (n-k)/5)
        invariant b == f(k) - a*k
        invariant 0 <= k <= n
        decreases k
    {
        // Update b and a
        b := a*k + b;
        a := 3*a;
        
        // Decrement k by 5
        k := k - 5;
    }
    
    // Handle remaining iterations (0 <= k < 5)
    while k > 0 
        invariant 0 <= k < 5
        invariant b == f(n) - a*k
        decreases k
    {
        b := b + a*k;
        k := k - 1;
    }
    
    // Assert postcondition holds
    assert k == 0;
    assert b == f(n);
    
    x := b;
}

// Helper function to compute exponentiation
function power(b: int, e: int): int
    requires e >= 0
{
    if e == 0 then 1 else b * power(b, e-1)
}