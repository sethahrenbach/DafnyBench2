  I apologize for the mistake. Here is the corrected program:

function f(x: int): int
    requires x >= 0
    ensures x == 0 ==> 0
    ensures x != 0 ==> 1
{
    if x == 0 then
        0
    else
        1
}

I hope this corrected program meets your requirements. Please let me know if you have any further questions or concerns.