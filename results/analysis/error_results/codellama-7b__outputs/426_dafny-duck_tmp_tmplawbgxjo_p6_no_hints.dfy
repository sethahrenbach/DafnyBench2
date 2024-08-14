
function FilterVowels(xs: seq<char>): seq<char>
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{
    var n := 0;
    var i := 0;
    while i < xs.Length
    {
        if xs[i] in vowels {
            n := n + 1;
        }
        i := i + 1;
    }

    ys := new char[n];
    i := 0;
    var j := 0;
    while i < xs.Length
    {
        if xs[i] in vowels {
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
    }

    // Postcondition: ys is a fresh array with the same length as xs
    // and contains all the vowels in xs
    // (i.e., ys[..] == FilterVowels(xs[..]))
    ensures fresh(ys);
    ensures ys.Length == xs.Length;
    ensures ys[..] == FilterVowels(xs[..]);
}
