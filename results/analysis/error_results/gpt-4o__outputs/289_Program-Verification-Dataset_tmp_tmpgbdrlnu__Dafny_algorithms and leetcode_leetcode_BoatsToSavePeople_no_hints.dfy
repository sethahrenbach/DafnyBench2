function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{
    if |s| == 1 then s[0] else s[0] + s[1]
}

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
    1 <= |boat| <= 2 && sumBoat(boat) <= limit
}

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
    if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
    multiset(xs) == multisetAdd(ss)
}

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}

predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
    boats := 0;
    var lower: nat := 0;
    var upper: int := |people| - 1;
    ghost var visitedUpper: multiset<nat> := multiset{};
    ghost var visitedLower: multiset<nat> := multiset{};
    ghost var remaining: multiset<nat> := multiset(people);
    ghost var safeBoats: seq<seq<nat>> := [];
    while lower <= upper 
        invariant 0 <= lower <= upper + 1 <= |people|
        invariant multisetEqual(safeBoats, people[..lower] + people[upper+1..])
        invariant allSafe(safeBoats, limit)
        invariant boats == |safeBoats|
        invariant visitedUpper + visitedLower + remaining == multiset(people)
        invariant visitedUpper + visitedLower == multiset(people[..lower] + people[upper+1..])
        invariant remaining == multiset(people[lower..upper+1])
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            boats := boats + 1;
            safeBoats := [[people[upper]]] + safeBoats;
            visitedUpper := visitedUpper + multiset{people[upper]};
            upper := upper - 1;
        } else {
            boats := boats + 1;
            if lower == upper {
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[lower]]] + safeBoats;
            } else {
                visitedUpper := visitedUpper + multiset{people[upper]};
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[upper], people[lower]]] + safeBoats;
                upper := upper - 1;
            }
            lower := lower + 1;
        }
        remaining := multiset(people[lower..upper+1]);
    }
    assert multisetEqual(safeBoats, people);
    assert allSafe(safeBoats, limit);
    assert boats == |safeBoats|;
}