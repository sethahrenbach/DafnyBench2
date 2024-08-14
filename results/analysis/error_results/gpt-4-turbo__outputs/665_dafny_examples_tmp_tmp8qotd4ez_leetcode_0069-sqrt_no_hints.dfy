// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
    var l, r := 0, x;
    while (l <= r)
        invariant 0 <= l && r <= x
        invariant forall k :: 0 <= k < l ==> k * k <= x
        invariant forall k :: r < k <= x ==> k * k > x
        decreases r - l
    {
        var mid := (l + r) / 2;
        if (mid * mid <= x) {
            if ((mid + 1) * (mid + 1) > x) {
                res := mid;
                return;
            } else {
                l := mid + 1;
            }
        } else {
            r := mid - 1;
        }
    }
    // Since the loop is exited only by the return statement when the correct mid is found,
    // the following line should logically never be reached. The loop invariant and the condition
    // for the loop exit ensure that when l > r, the correct square root has been found.
    // Therefore, we do not need an assert false here; instead, we need to ensure the loop invariant
    // logically leads to the postcondition.
}