
function InsertionSort(s: seq<int>) returns (r: seq<int>)
    ensures r == s;
    ensures IsSorted(r);
{
    var i := 0;
    var j := 0;
    var x := s[i];
    var y := s[j];
    while j < |s| {
        if x < y {
            r := r[..i] + [x] + r[i..j] + [y] + r[j..];
            i := i + 1;
            j := j + 1;
            x := s[i];
            y := s[j];
        } else {
            r := r[..i] + [y] + r[i..j] + [x] + r[j..];
            j := j + 1;
            x := s[i];
            y := s[j];
        }
    }
    return r;
}
