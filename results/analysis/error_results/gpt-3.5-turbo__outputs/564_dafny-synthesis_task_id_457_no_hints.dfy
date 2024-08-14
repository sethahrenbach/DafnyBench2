
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{
    minSublist := s[0];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant minSublist in s
        invariant forall sublist :: sublist in s ==> |minSublist| <= |sublist|
    {
        if |s[i]| < |minSublist| {
            minSublist := s[i];
        }
        i := i + 1;
    }
}
