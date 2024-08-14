
function Fat(n: nat): nat
{
   if n == 0 then 1 else n * Fat(n-1)
}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
    // loop invariant: r is the product of all integers from 1 to n
    loop invariant r == Fat(n)
    // precondition: n >= 0
    precondition n >= 0
    // postcondition: the result is equal to the factorial of n
    postcondition r == Fat(n)

    r := 1;
    var i := 0;
    while i < n
    {
        // loop invariant: r is the product of all integers from 1 to i
        loop invariant r == Fat(i)
        // precondition: i >= 0
        precondition i >= 0
        // postcondition: the result is equal to the product of all integers from 1 to i
        postcondition r == Fat(i)

        i := i + 1;
        r := r * i;
    }
}
