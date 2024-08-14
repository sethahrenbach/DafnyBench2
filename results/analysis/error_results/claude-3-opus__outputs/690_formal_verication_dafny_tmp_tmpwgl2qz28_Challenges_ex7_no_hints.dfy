// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
    t := s;
    t := t[ x := s[y]];
    t := t[ y := s[x] ];
    return t;
}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
{
    sobases := bases;
    var c, next:nat := 0, 0;
    var g, t:nat := |bases|, |bases|;

    while next != g
    invariant 0 <= c <= next <= g <= t <= |bases|
    invariant forall i :: 0 <= i < c ==> sobases[i] == A
    invariant forall i :: c <= i < next ==> sobases[i] == C
    invariant forall i :: g <= i < t ==> sobases[i] == G
    invariant forall i :: t <= i < |bases| ==> sobases[i] == T
    invariant multiset(bases) == multiset(sobases)
    decreases g - next
    {
        match(sobases[next]) {
            case C => next := next + 1;
            case A => sobases := Exchanger(sobases, next, c);
                    c, next:= c + 1, next + 1;
            case G => assert next < g;
                    g := g - 1;
                    sobases := Exchanger(sobases, next, g);
            case T => assert next < g <= t;
                    g , t:= g - 1, t - 1;
                    sobases := Exchanger(sobases, next, t);
                    if (g != t) {
                        assert next < g;
                        sobases := Exchanger(sobases, next, g);
                    }
        }
    }

    assert c == next == g == t;
    assert forall i :: 0 <= i < c ==> sobases[i] == A;
    assert forall i :: c <= i < g ==> sobases[i] == C;
    assert forall i :: g <= i < t ==> sobases[i] == G;
    assert forall i :: t <= i < |bases| ==> sobases[i] == T;
    assert bordered(sobases);

    return sobases;
}

method Testerexchange() {
    var a:seq<Bases> := [A, C, A, T]; 
    var b:seq<Bases> := Exchanger(a, 2, 3);
    assert b == [A, C, T, A];

    var c:seq<Bases> := [A, C, A, T, A, T, C];     
    var d:seq<Bases> := Exchanger(c, 5, 1);
    assert d == [A, T, A, T, A, C, C];

    var e:seq<Bases> := [A, C, A, T, A, T, C];     
    var f:seq<Bases> := Exchanger(e, 1, 1);
    assert f == [A, C, A, T, A, T, C];

    var g:seq<Bases> := [A, C];     
    var h:seq<Bases> := Exchanger(g, 0, 1);
    assert h == [C, A];
}

method Testsort() {
    var a:seq<Bases> := [G,A,T];
    var b:seq<Bases> := Sorter(a);
    assert b == [A,G,T];

    var c:seq<Bases> := [G, A, T, T, A, C, G, C, T, A, C, G, T, T, G];
    var d:seq<Bases> := Sorter(c);
    assert d == [A, A, A, C, C, C, G, G, G, G, T, T, T, T, T];

    var e:seq<Bases> := [A];
    var f:seq<Bases> := Sorter(e);
    assert f == [A];

    var g:seq<Bases> := [A, C, G, T];
    var h:seq<Bases> := Sorter(g);
    assert h == [A, C, G, T];

    var i:seq<Bases> := [A, T, C, T, T];
    var j:seq<Bases> := Sorter(i);
    assert j == [A, C, T, T, T];
}