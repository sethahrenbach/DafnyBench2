function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        assert reverse([] + ys) == reverse(ys);
        assert reverse(ys) + reverse([]) == reverse(ys);
    } else {
        ReverseAppendDistr(xs[1..], ys);
        assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
        assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
        assert reverse(xs[1..] + ys) == reverse(ys) + reverse(xs[1..]);
        assert reverse(xs + ys) == reverse(ys) + reverse(xs[1..]) + [xs[0]];
        assert reverse(xs + ys) == reverse(ys) + reverse(xs);
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
    ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
        assert reverse([]) == [];
        assert reverse(reverse([])) == [];
    } else {
        ReverseInvolution(xxs[1..]);
        ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]);
        assert reverse([xxs[0]]) == [xxs[0]];
        assert reverse(reverse(xxs[1..]) + [xxs[0]]) == reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
        assert reverse(reverse(xxs[1..]) + [xxs[0]]) == [xxs[0]] + xxs[1..];
        assert reverse(reverse(xxs)) == xxs;
    }
}