ghost function Hash(s:string):int {
    SumChars(s) % 137
}

ghost function SumChars(s: string):int {
    if |s| == 0 then 0 else 
        s[|s| - 1] as int + SumChars(s[..|s| -1])
}

class CheckSumCalculator{
    var data: string
    var cs:int

    ghost predicate Valid()
        reads this
    {
        cs == Hash(data)
    }

    constructor ()
        ensures Valid() && data == ""
    {
        data, cs := "", 0;
    }

    method Append(d:string)
        requires Valid()
        modifies this
        ensures Valid() && data == old(data) + d
    {
        var i := 0;
        while i != |d| 
            invariant 0 <= i <= |d|
            invariant data == old(data) + d[..i]
            invariant cs == Hash(old(data) + d[..i])
        {
            cs := (cs + d[i] as int) % 137;
            data := data + d[i];  // Corrected to direct concatenation of char to string
            i := i + 1;
        }
    }

    function GetData(): string
        requires Valid()
        reads this
        ensures Hash(GetData()) == Checksum()
    {
        data
    }

    function Checksum(): int 
        requires Valid()
        reads this 
        ensures Checksum() == Hash(data)
    {
        cs
    }
}

method Main() {
    var newSeq := ['a','b','c','d','e','f','g','h'];
    var newSeqTwo := ['h','g','f','e','d','c','b','a'];
    var newSet : set<int>;
    newSet := {1,2,3,4,5};
    var newSetTwo := {6,7,8,9,10};

    print "element is newset ",   newSet,"\n";

    var newArray := new int [99];
    newArray[0] := 99;
    newArray[1] := 2;

    print "element is ?  ", newArray.Length,"\n";  // Corrected |newArray| to newArray.Length
    var tmpSet := {'a','c'};
    var tmpFresh := {'c'};
    print "tmp is ",   tmpSet - tmpFresh;

    var newMap := map[];
    newMap := newMap[1:=2];
    var nnewMap := map[3:=444];
    print "keys is ",newMap.Keys,newMap.Values;
    print "value is", nnewMap.Keys,nnewMap.Values;
}