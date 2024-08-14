// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{
    if r1 < r2 {
        assert r1*r1 <= x && (r1+1)*(r1+1) > x;
        assert r2*r2 <= x && (r2+1)*(r2+1) > x;
        assert (r1+1)*(r1+1) <= r2*r2;
        assert (r1+1)*(r1+1) <= x;
        assert false;
    } else if r2 < r1 {
        assert r1*r1 <= x && (r1+1)*(r1+1) > x;
        assert r2*r2 <= x && (r2+1)*(r2+1) > x;
        assert (r2+1)*(r2+1) <= r1*r1;
        assert (r2+1)*(r2+1) <= x;
        assert false;
    }
}

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
    var l, r := 0, x;
    while (l <= r)
        invariant 0 <= l && l <= r + 1 && r <= x;
        invariant exists k :: (0 <= k && k*k <= x && (k+1)*(k+1) > x && l <= k && k <= r);
    {
        var mid := (l + r) / 2;
        if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
            assert mid*mid <= x;
            assert (mid+1)*(mid+1) > x;
            assert sqrt(x, mid);
            return mid;
        } else if (mid * mid <= x) {
            l := mid + 1;
            assert l > mid;
        } else {
            r := mid - 1;
            assert r < mid;
        }
    }
    assert false; // This line should never be reached
}