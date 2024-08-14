// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
{
    k := 0;
    if a[500] < x   { k := 489;   }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k   k+511  1000
    if a[k+255] < x { k := k+256; }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k   k+255  1000
    if a[k+127] < x { k := k+128; }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+63] < x  { k := k+64;  }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+31] < x  { k := k+32;  }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+15] < x  { k := k+16;  }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+7] < x   { k := k+8;   }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+3] < x   { k := k+4;   }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    if a[k+1] < x   { k := k+2;   }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    // a: | <x | ??? | >= x|
    //     ^    ^     ^     ^
    //     0    k    k+1   1000
    if a[k] < x     { k := k+1;   }
    assert 0 <= k <= 1000;
    assert forall r | 0 <= r < k :: a[r] < x;
    assert forall r | k <= r < 1000 :: a[r] >= x;
    // a: | <x | >= x|
    //     ^    ^     ^
    //     0    k    1000
}

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{
    k := i;
    var c := n;
    while c != 0
        invariant i <= k <= i+n
        invariant 0 <= c <= n
        invariant Is2Pow(c+1)
        invariant forall r | i <= r < k :: a[r] < x
        invariant forall r | k <= r < i+n :: a[r] >= x
        decreases c
    {
        assert k + c < a.Length;
        c := c/2;
        if a[k+c] < x { k := k+c+1; }
    }
}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
    decreases n
{
    if n==0 { return i; }
    if a[i+n/2] < x
    {
        k := Search2PowRecursive(a,i+n/2+1,n/2,x);
    }
    else
    {
        k := Search2PowRecursive(a,i,n/2,x);
    }
}