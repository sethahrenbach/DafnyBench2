
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
        invariant lower <= upper + 1
        invariant sorted(people)
        invariant multiset(people) == visitedUpper + visitedLower + multiset(people[lower..upper+1])
        invariant allSafe(safeBoats, limit)
        invariant boats == |safeBoats|
        decreases upper - lower
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            boats := boats + 1;
            safeBoats := safeBoats + [[people[upper]]];
            visitedUpper := visitedUpper + multiset{people[upper]};
            upper := upper - 1;
        } else {
            boats := boats + 1;
            if lower == upper {
                safeBoats := safeBoats + [[people[lower]]];
                visitedLower := visitedLower + multiset{people[lower]};
                lower := lower + 1; // Corrected to increment lower to avoid infinite loop
            } else {
                safeBoats := safeBoats + [[people[upper], people[lower]]];
                visitedUpper := visitedUpper + multiset{people[upper]};
                visitedLower := visitedLower + multiset{people[lower]};
                upper := upper - 1;
                lower := lower + 1;
            }
        }
    }
}
