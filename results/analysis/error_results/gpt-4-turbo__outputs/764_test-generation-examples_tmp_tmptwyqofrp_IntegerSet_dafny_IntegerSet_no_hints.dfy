module IntegerSet {

    class Set {

        var elements: seq<int>;

        constructor Set0() 
        ensures this.elements == []
        ensures |this.elements| == 0
        {
            this.elements := [];
        }

        constructor Set(elements: seq<int>)
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures this.elements == elements
        ensures forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements|  && j != i:: this.elements[i] != elements[j]
        {
            this.elements := elements;
        }

        method size() returns (size : int)
        ensures size == |elements|
        {
            size := |elements|;
        }

        method addElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> elements == old(elements)
        ensures element !in old(elements) ==> |elements| == |old(elements)| + 1 && element in elements && forall i : int :: i in old(elements) ==> i in elements
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {
            if (element !in elements) {
                elements := elements + [element];
            }
        }

        method removeElement(element : int)
        modifies this`elements
        requires forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        ensures element in old(elements) ==> |elements| == |old(elements)| - 1 && (forall i : int :: i in old(elements) && i != element <==> i in elements) && element !in elements
        ensures element !in old(elements) ==> elements == old(elements)
        ensures forall i, j | 0 <= i < |elements| && 0 <= j < |elements| && j != i :: elements[i] != elements[j]
        {
            if (element in elements) {
                var i := 0;

                while (0 <= i < |elements|)
                    decreases |elements| - i
                    invariant 0 <= i <= |elements|
                    invariant forall k, l | 0 <= k < i && 0 <= l < |elements| && k != l :: elements[k] != elements[l]
                    invariant forall x | x in old(elements) && x != element :: x in elements
                    invariant element !in elements[i..]
                {
                    if (elements[i] == element) {
                        elements := elements[..i] + elements[i+1..];
                        break;
                    }
                    i := i + 1;
                }
            }
        }

        method contains(element : int) returns (contains : bool)
        ensures contains == (element in elements)
        ensures elements == old(elements)
        {
            contains := false;
            if (element in elements) {
                contains := true;
            }
        }

        function intersect_length(s1 : seq<int>, s2 : seq<int>, count : int, start : int, stop : int) : int 
        requires 0 <= start <= stop
        requires stop <= |s1|
        {
            if start == stop then count else (if s1[start] in s2 then intersect_length(s1, s2, count + 1, start + 1, stop) else intersect_length(s1, s2, count, start + 1, stop))
        }

        function union_length(s1 : seq<int>, s2 : seq<int>, count : int, i : int, stop : int) : int 
        requires 0 <= i <= stop
        requires stop <= |s1|
        {
            if i == stop then count else (if s1[i] !in s2 then union_length(s1, s2, count + 1, i + 1, stop) else union_length(s1, s2, count, i + 1, stop))
        }

        method intersect(s : Set) returns (intersection : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in intersection.elements <==> i in s.elements && i in this.elements 
        ensures forall i : int :: i !in intersection.elements  <==> i !in s.elements || i !in this.elements
        ensures forall j, k | 0 <= j < |intersection.elements| && 0 <= k < |intersection.elements| && j != k :: intersection.elements[j] != intersection.elements[k]
        ensures fresh(intersection)
        {
            intersection := new Set.Set0();
            var inter: seq<int> := [];

            var i := 0;
            while (0 <= i < |this.elements|)
                decreases |this.elements| - i
                invariant 0 <= i <= |this.elements|
                invariant forall x | x in inter :: x in s.elements && x in this.elements
                invariant forall x | x in this.elements[0..i] && x in s.elements :: x in inter
                invariant forall j, k | 0 <= j < |inter| && 0 <= k < |inter| && j != k :: inter[j] != inter[k]
            {
                if (this.elements[i] in s.elements && this.elements[i] !in inter) {
                    inter := inter + [this.elements[i]];
                }
                i := i + 1;
            }
            intersection.elements := inter;
        }

        method union(s : Set) returns (union : Set)
        requires forall i, j | 0 <= i < |s.elements| && 0 <= j < |s.elements| && i != j :: s.elements[i] != s.elements[j]
        requires forall i, j | 0 <= i < |this.elements| && 0 <= j < |this.elements| && i != j :: this.elements[i] != this.elements[j]
        ensures forall i : int :: i in s.elements || i in this.elements <==> i in union.elements
        ensures forall i : int :: i !in s.elements && i !in this.elements <==> i !in union.elements
        ensures forall j, k | 0 <= j < |union.elements| && 0 <= k < |union.elements| && j != k :: union.elements[j] != union.elements[k]
        ensures fresh(union)
        {
            var elems := s.elements;
            union := new Set.Set0();

            var i := 0;
            while (0 <= i < |this.elements|)
                decreases |this.elements| - i
                invariant 0 <= i <= |this.elements|
                invariant forall x | x in elems :: x in s.elements || x in this.elements[0..i]
                invariant forall x | x in this.elements[0..i] :: x in elems
                invariant forall j, k | 0 <= j < |elems| && 0 <= k < |elems| && j != k :: elems[j] != elems[k]
            {
                if (this.elements[i] !in elems) {
                    elems := elems + [this.elements[i]];
                }
                i := i + 1;
            }

            union.elements := elems;
        }
    }
}