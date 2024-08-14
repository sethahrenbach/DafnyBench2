
function numRescueBoats(people: seq<nat>, limit: nat): nat
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
    var boats := 0;
    var lower := 0;
    var upper := |people| - 1;
    var visitedUpper := multiset{};
    var visitedLower := multiset{};
    var remaining := multiset(people);
    var safeBoats := seq{};
    while lower <= upper
    {
        if people[upper] == limit || people[upper] + people[lower] > limit
        {
            boats := boats + 1;
            safeBoats := seq{people[upper]} + safeBoats;
            visitedUpper := visitedUpper + multiset{people[upper]};
            upper := upper - 1;
        }
        else
        {
            visitedLower := visitedLower + multiset{people[lower]};
            boats := boats + 1;
            if lower == upper
            {
                safeBoats := seq{people[lower]} + safeBoats;
            }
            else
            {
                visitedUpper := visitedUpper + multiset{people[upper]};
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := seq{people[upper], people[lower]} + safeBoats;
                upper := upper - 1;
            }
            lower := lower + 1;
        }
    }
    return boats;
}
