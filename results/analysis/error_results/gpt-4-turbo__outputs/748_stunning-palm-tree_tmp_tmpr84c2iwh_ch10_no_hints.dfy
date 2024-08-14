
module PQueue {
    export provides PQueue
    export provides Empty, IsEmpty, Insert, RemoveMin
    export provides Valid, Elements
    export reveals IsMin

    type PQueue = BraunTree
    datatype BraunTree =
        | Leaf
        | Node(x: int, left: BraunTree, right: BraunTree)

    function Empty(): PQueue {
        Leaf
    }

    predicate IsEmpty(pq: PQueue) {
        pq == Leaf
    }

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) =>
            if y < x then
                Node(y, Insert(right, x), left)
            else
                Node(x, Insert(right, y), left)
    }

    function RemoveMin(pq: PQueue): (int, PQueue)
      requires Valid(pq) && !IsEmpty(pq)
    {
        var Node(x, left, right) := pq;
        (x, DeleteMin(pq))
    }
    
    function DeleteMin(pq: PQueue): PQueue
      requires IsBalanced(pq) && !IsEmpty(pq)
    {
        if pq.right.Leaf? then
            pq.left
        else if pq.left.x <= pq.right.x then
            Node(pq.left.x, pq.right, DeleteMin(pq.left))
        else
            Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
    }

    function ReplaceRoot(pq: PQueue, r: int): PQueue
        requires !IsEmpty(pq)
    {
        if pq.left.Leaf? ||
            (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x))
        then
            Node(r, pq.left, pq.right)
        else if pq.right.Leaf? then
            Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
        else if pq.left.x < pq.right.x then
            Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
        else
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
    }

    ghost function Elements(pq: PQueue): multiset<int> {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) => multiset{x} + Elements(left) + Elements(right)
    }

    ghost predicate Valid(pq: PQueue) {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }

    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left.Leaf? || x <= left.x) &&
            (right.Leaf? || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) =>
            IsBalanced(left) && IsBalanced(right) &&
            var L, R := |Elements(left)|, |Elements(right)|;
            L == R || L == R + 1
    }

    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }
}

module PQueueClient {
    import PQ = PQueue

    method Client() {
        var pq := PQ.Empty();
        assert PQ.Valid(pq);
        assert PQ.Elements(pq) == multiset{};

        pq := PQ.Insert(pq, 1);
        assert PQ.Valid(pq);
        assert PQ.Elements(pq) == multiset{1};

        pq := PQ.Insert(pq, 2);
        assert PQ.Valid(pq);
        assert PQ.Elements(pq) == multiset{1, 2};

        var (min, pq1) := PQ.RemoveMin(pq);
        assert min == 1;
        assert PQ.Valid(pq1);
        assert PQ.Elements(pq1) == multiset{2};

        assert !PQ.IsEmpty(pq1);
    }
}
