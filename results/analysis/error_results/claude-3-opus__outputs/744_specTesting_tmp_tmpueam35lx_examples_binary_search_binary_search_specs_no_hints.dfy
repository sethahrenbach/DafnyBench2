lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
        invariant 0 <= lo <= hi <= |intSeq|
        invariant forall i | 0 <= i < lo :: intSeq[i] < key
        invariant forall i | hi <= i < |intSeq| :: intSeq[i] > key
        decreases hi - lo
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            return mid;
        }
    }
    return -1;
}

predicate BinarySearchTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

lemma BinarySearchDeterministic(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
        invariant 0 <= lo <= hi <= |intSeq|
        invariant forall i | 0 <= i < lo :: intSeq[i] < key
        invariant forall i | hi <= i < |intSeq| :: intSeq[i] > key
        invariant lo < hi ==> exists i | lo <= i < hi :: intSeq[i] == key
        decreases hi - lo
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    if lo < |intSeq| && intSeq[lo] == key {
        return lo;
    } else {
        return -1;
    }
}

predicate BinarySearchDeterministicTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong1(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key // i >= 0
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

predicate BinarySearchWrong1Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key) // i >= 0
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong2(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key // i < |intSeq|
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

predicate BinarySearchWrong2Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key) // i < |intSeq|
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong3(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r < 0 || (r < |intSeq| && intSeq[r] == key) // post condition not correctly formed
{
    return -1;
}

predicate BinarySearchWrong3Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    r < 0 || (r < |intSeq| && intSeq[r] == key)
}

lemma BinarySearchWrong4(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures 0 <= r < |intSeq| && intSeq[r] == key

predicate BinarySearchWrong4Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    0 <= r < |intSeq| && intSeq[r] == key
}