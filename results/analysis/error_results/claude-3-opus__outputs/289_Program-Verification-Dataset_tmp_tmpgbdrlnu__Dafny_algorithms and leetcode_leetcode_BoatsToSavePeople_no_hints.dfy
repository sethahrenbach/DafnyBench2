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
    ghost var safeBoats: seq<seq<nat>> := [];

    while lower <= upper
        invariant 0 <= lower <= |people|
        invariant -1 <= upper < |people|
        invariant lower <= upper + 1
        invariant boats == |safeBoats|
        invariant allSafe(safeBoats, limit)
        invariant multisetEqual(safeBoats, people[..lower] + people[upper+1..])
        invariant forall boat :: boat in safeBoats ==> forall p :: p in boat ==> p in people[lower..upper+1]
        decreases upper - lower
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            boats := boats + 1;
            safeBoats := safeBoats + [[people[upper]]];
            upper := upper - 1;
        } else {
            boats := boats + 1;
            if lower == upper {
                safeBoats := safeBoats + [[people[lower]]];
                lower := lower + 1;
            } else {
                safeBoats := safeBoats + [[people[lower], people[upper]]];
                upper := upper - 1;
                lower := lower + 1;
            }
        }
    }
    assert multisetEqual(safeBoats, people[..lower] + people[upper+1..]);
    assert lower > upper;
    assert people[..lower] + people[upper+1..] == people;
    assert multisetEqual(safeBoats, people);
}