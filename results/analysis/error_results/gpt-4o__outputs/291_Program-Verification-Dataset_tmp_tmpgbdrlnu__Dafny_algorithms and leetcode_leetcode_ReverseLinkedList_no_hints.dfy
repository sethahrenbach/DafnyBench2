datatype ListNode = Null | Node(val: nat, next: ListNode)

function reverse<A>(x: seq<A>): seq<A> 
{
    if x == [] then [] else reverse(x[1..])+[x[0]]
}

function nodeConcat(xs: ListNode, end: ListNode): ListNode {
    if xs == Null then end else Node(xs.val, nodeConcat(xs.next, end))
}

function reverseList(xs: ListNode): ListNode
{
    if xs == Null then Null else nodeConcat(reverseList(xs.next), Node(xs.val, Null))
}

lemma ConcatNullIsRightIdentity(xs: ListNode) 
    ensures xs == nodeConcat(xs, Null)
{
    if xs == Null {
    } else {
        ConcatNullIsRightIdentity(xs.next);
    }
}

lemma ConcatNullIsLeftIdentity(xs: ListNode) 
    ensures xs == nodeConcat(Null, xs)
{
    // Trivial
}

lemma ConcatExtensionality(xs: ListNode)
    requires xs != Null
    ensures nodeConcat(Node(xs.val, Null), xs.next) == xs;
{
    // Trivial
}

lemma ConcatAssociative(xs: ListNode, ys: ListNode, zs: ListNode)
    ensures nodeConcat(nodeConcat(xs, ys), zs) == nodeConcat(xs, nodeConcat(ys, zs))
{
    if xs == Null {
        // Trivial
    } else {
        ConcatAssociative(xs.next, ys, zs);
    }
}

lemma reverseSingleList(xs: ListNode) 
    requires xs != Null
    requires xs.next == Null
    ensures reverseList(xs) == xs
{
    // Trivial
}

lemma {:verify true} ConcatReverseList(xs: ListNode, ys: ListNode) 
    ensures reverseList(nodeConcat(xs, ys)) == nodeConcat(reverseList(ys), reverseList(xs))
{
    if xs == Null {
        calc {
            reverseList(nodeConcat(xs, ys));
            == {ConcatNullIsLeftIdentity(ys);}
            reverseList(ys);
            == {ConcatNullIsRightIdentity(reverseList(ys));}
            nodeConcat(reverseList(ys), Null);
            nodeConcat(reverseList(ys), xs);
            nodeConcat(reverseList(ys), reverseList(xs));
        }
    } else {
        var x := Node(xs.val, Null);
        calc {
            reverseList(nodeConcat(xs, ys));
            == {ConcatAssociative(x, xs.next, ys);}
            reverseList(nodeConcat(x, nodeConcat(xs.next, ys)));
            == {ConcatReverseList(xs.next, ys);}
            nodeConcat(reverseList(nodeConcat(xs.next, ys)), x);
            == {ConcatAssociative(reverseList(ys), reverseList(xs.next), x);}
            nodeConcat(reverseList(ys), nodeConcat(reverseList(xs.next), x));
            nodeConcat(reverseList(ys), reverseList(xs));
        }
    }
}

lemma reverseReverseListIsIdempotent(xs: ListNode)
    ensures reverseList(reverseList(xs)) == xs
{
    if xs == Null {
        // Trivial
    } else {
        var x := Node(xs.val, Null);
        calc {
            reverseList(reverseList(xs));
            == {reverseReverseListIsIdempotent(xs.next);}
            reverseList(reverseList(nodeConcat(x, xs.next)));
            == {ConcatReverseList(x, xs.next);}
            reverseList(nodeConcat(reverseList(xs.next), reverseList(x)));
            == {ConcatReverseList(reverseList(xs.next), x);}
            nodeConcat(reverseList(x), reverseList(reverseList(xs.next)));
            == {reverseReverseListIsIdempotent(xs.next);}
            nodeConcat(x, xs.next);
            xs;
        }
    }
}

lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>) 
    ensures multiset(xs) == multiset(reverse(xs))
{
    if xs == [] {
        // Trivial
    } else {
        reversePreservesMultiset(xs[1..]);
    }
}

lemma reversePreservesLength<A>(xs: seq<A>)
    ensures |xs| == |reverse(xs)|
{
    if xs == [] {
        // Trivial
    } else {
        reversePreservesLength(xs[1..]);
    }
}

lemma lastReverseIsFirst<A>(xs: seq<A>)
    requires |xs| > 0
    ensures xs[0] == reverse(xs)[|reverse(xs)|-1]
{
    reversePreservesLength(xs);
}

lemma firstReverseIsLast<A>(xs: seq<A>)
    requires |xs| > 0
    ensures reverse(xs)[0] == xs[|xs|-1]
{
    reversePreservesLength(xs);
}

lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if |xs| == 0 {
        // Trivial
    } else {
        ReverseConcat(xs[1..], ys);
    }
}

lemma reverseRest<A>(xs: seq<A>)
    requires |xs| > 0
    ensures reverse(xs) == [xs[|xs|-1]] + reverse(xs[0..|xs|-1])
{
    firstReverseIsLast(xs);
    calc {
        reverse(xs);
        == {ReverseConcat(xs[0..|xs|-1], [xs[|xs|-1]]);}
        reverse(xs[0..|xs|-1] + [xs[|xs|-1]]);
        reverse([xs[|xs|-1]]) + reverse(xs[0..|xs|-1]);
    }
}

lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
    requires |xs| == |ys|
    requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
    ensures xs == ys
{
    if |xs| == 0 {
        // Trivial
    } else {
        SeqEq(xs[1..], ys[1..]);
    }
}

lemma ReverseIndexAll<T>(xs: seq<T>)
    ensures |reverse(xs)| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
{
    if |xs| == 0 {
        // Trivial
    } else {
        ReverseIndexAll(xs[1..]);
    }
}

lemma ReverseIndex<T>(xs: seq<T>, i: int)
    requires 0 <= i < |xs|
    ensures |reverse(xs)| == |xs|
    ensures reverse(xs)[i] == xs[|xs| - i - 1]
{
    ReverseIndexAll(xs);
}

lemma ReverseSingle<A>(xs: seq<A>) 
    requires |xs| == 1
    ensures reverse(xs) == xs
{
    // Trivial
}

lemma reverseReverseIdempotent<A>(xs: seq<A>) 
    ensures reverse(reverse(xs)) == xs
{
    if xs == [] {
        // Trivial
    } else {
        calc {
            reverse(reverse(xs));
            == {ReverseConcat([xs[0]], xs[1..]);}
            reverse(reverse(xs[1..]) + reverse([xs[0]]));
            == {ReverseSingle([xs[0]]);}
            reverse(reverse(xs[1..]) + [xs[0]]);
            == {ReverseConcat(reverse(xs[1..]), [xs[0]]);}
            reverse([xs[0]]) + reverse(reverse(xs[1..]));
            [xs[0]] + reverse(reverse(xs[1..]));
            == {reverseReverseIdempotent(xs[1..]);}
            xs;
        }
    }
}

method hasCycle(head: ListNode): bool
{
    var leader := head;
    var follower := head;
    while leader != Null
        invariant leader != Null ==> leader in listNodes(head)
        invariant follower != Null ==> follower in listNodes(head)
        invariant leader != Null ==> acyclic(head, leader)
        invariant follower != Null ==> acyclic(head, follower)
    {
        leader := leader.next;
        if follower != Null && follower.next != Null {
            follower := follower.next.next;
        } else if follower != Null && follower.next == Null {
            follower := follower.next;
        }
        if follower == leader && follower != Null {
            return true;
        }
    }
    return false;
}

predicate listNodes(xs: ListNode)
    decreases xs
{
    xs == Null || xs in listNodes(xs.next)
}

predicate acyclic(xs: ListNode, end: ListNode)
    decreases xs
{
    xs == end || (xs != Null && acyclic(xs.next, end))
}

method test() {
    var cycle := Node(1, Null);
    var next := Node(2, cycle);
    // cycle.next := next; // Commented out to avoid compilation error
}
