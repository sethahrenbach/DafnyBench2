predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method IsInteger(s: string) returns (result: bool)
    ensures result <==> (|s| > 0) && (forall i :: 0 <= i < |s| ==> IsDigit(s[i]))
{
    if |s| == 0 {
        result := false;
    } else {
        result := true;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant result ==> (forall j :: 0 <= j < i ==> IsDigit(s[j]))
            invariant !result ==> exists j :: 0 <= j < i && !IsDigit(s[j])
            invariant !result ==> |s| > 0
        {
            if !IsDigit(s[i]) {
                result := false;
            }
            i := i + 1;
        }
    }
}