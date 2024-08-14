/*
 * Task 2: Define the natural numbers as an algebraic data type
 * 
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 */
datatype Nat = Zero | S(Pred: Nat)

/// Task 2
// Exercise (a'): proving that the successor constructor is injective
/*
 * It's known that the successors are equal.
 * It's know that for equal inputs, a non-random function returns the same result.
 * Thus, the predecessors of the successors, namely, the numbers themselves, are equal.
 */
lemma SIsInjective(x: Nat, y: Nat)
    ensures S(x) == S(y) ==> x == y
{
    if S(x) == S(y) {
        assert x == y; // Injectivity of S
    }
}

// Exercise (a''): Zero is different from successor(x), for any x
/*
 * For all x: Nat, S(x) is built using the S constructor, implying that S(x).Zero? is inherently false.
 */
lemma ZeroIsDifferentFromSuccessor(n: Nat)
    ensures S(n) != Zero
{
    assert S(n).S?; // S(n) is constructed using S
    assert !S(n).Zero?; // S(n) is not Zero
}

// Exercise (b): inductively defining the addition of natural numbers
/*
 * The function decreases y until it reaches the base inductive case.
 * The Addition between Zero and a x: Nat will be x.
 * The Addition between a successor of a y': Nat and another x: Nat is the successor of the Addition between y' and x
 *
 * x + y = 1 + ((x - 1) + y)
 */
function Add(x: Nat, y: Nat) : Nat
    decreases y
{
    match y
        case Zero => x
        case S(y') => S(Add(x, y')) 
}

// Exercise (c'): proving that the addition is commutative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Neutral.
 */
 lemma {:induction n} ZeroAddNeutral(n: Nat)
    ensures Add(n, Zero) == Add(Zero, n) == n
    decreases n
{
    match n
        case Zero => {
            assert Add(Zero, Zero) == Zero;
            assert Add(Zero, n) == n;
        }
        case S(n') => {
            ZeroAddNeutral(n');
            assert Add(S(n'), Zero) == S(n');
            assert Add(Zero, S(n')) == S(n');
            assert Add(Zero, n) == n;
        }
}

/*
 * Since Zero is neutral, it is trivial that the order of addition is not of importance.
 */
lemma {:induction n} ZeroAddCommutative(n: Nat)
    ensures Add(Zero, n) == Add(n, Zero)
    decreases n
{
    ZeroAddNeutral(n);
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y} AddCommutative(x: Nat, y: Nat)
    ensures Add(x, y) == Add(y, x)
    decreases x, y
{
    match x
        case Zero => ZeroAddCommutative(y);
        case S(x') => {
            AddCommutative(x', y);
            assert Add(S(x'), y) == S(Add(x', y));
            assert Add(y, S(x')) == S(Add(y, x'));
        }
}

// Exercise (c''): proving that the addition is associative
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that the Addition with Zero is Associative.
 *
 * Again, given that addition with Zero is neutral, the order of calculations is irrelevant.
 */
lemma {:induction x, y} ZeroAddAssociative(x: Nat, y: Nat)
    ensures Add(Add(Zero, x), y) == Add(Zero, Add(x, y))
    decreases x, y
{
    ZeroAddNeutral(x);
    assert Add(x, y) == Add(Zero, Add(x, y));
}

/*
 * Since now the base case of commutative addition with Zero is proven, we can now prove using induction.
 */
lemma {:induction x, y} AddAssociative(x: Nat, y: Nat, z: Nat)
    ensures Add(Add(x, y), z) == Add(x, Add(y, z))
    decreases x, y, z
{
    match z
        case Zero => ZeroAddAssociative(Add(x, y), Zero);
        case S(z') => {
            AddAssociative(x, y, z');
            assert Add(Add(x, y), S(z')) == S(Add(Add(x, y), z'));
            assert Add(x, Add(y, S(z'))) == S(Add(x, Add(y, z')));
        }
}

// Exercise (d): defining a predicate lt(m, n) that holds when m is less than n
/*
 * If x is Zero and y is a Successor, given that we have proven ZeroIsDifferentFromSuccessor for all x, the predicate holds.
 * Otherwise, if both are successors, we inductively check their predecessors.
 */
predicate LessThan(x: Nat, y: Nat)
{
    (x.Zero? && y.S?) || (x.S? && y.S? && LessThan(x.Pred, y.Pred))
}

// Exercise (e): proving that lt is transitive
/*
 * It is necessary, as with any induction, to have a proven base case.
 * In this case, we first prove that LessThan is Transitive having a Zero as the left-most parameter.
 *
 * We prove this statement using Reductio Ad Absurdum.
 * We suppose that Zero is not smaller that an arbitrary z that is non-Zero.
 * This would imply that Zero has to be a Successor (i.e. Zero.S? == true).
 * This is inherently false.
 */
lemma {:induction y, z} LessThanIsTransitiveWithZero(y: Nat, z: Nat)
    requires LessThan(Zero, y)
    requires LessThan(y, z)
    ensures LessThan(Zero, z)
    decreases y, z
{
    if !LessThan(Zero, z) {
        assert z.Zero?; // z must be Zero
        assert !y.Zero?; // y cannot be Zero since LessThan(Zero, y)
        assert false; // Contradiction
    }
}

/*
 * Since now the base case of transitive LessThan with Zero is proven, we can now prove using induction.
 *
 * In this case, the induction decreases on all three variables, all x, y, z until the base case.
 */
lemma {:induction x, y, z} LessThanIsTransitive(x: Nat, y: Nat, z: Nat)
    requires LessThan(x, y)
    requires LessThan(y, z)
    ensures LessThan(x, z)
    decreases x, y, z
{
    match x
        case Zero => LessThanIsTransitiveWithZero(y, z);
        case S(x') => {
            match y
                case S(y') => {
                    match z    
                        case S(z') => {
                            LessThanIsTransitive(x', y', z');
                            assert LessThan(x', z');
                            assert LessThan(x, z);
                        }
                }
        }
}

/// Task 3: Define the parametric lists as an algebraic data type
/*
 * Being an inductive data type, it's required that we have a base case constructor and an inductive one.
 * The inductive Append constructor takes as input a Nat, the head, and a tail, the rest of the list.
 */
datatype List<T> = Nil | Append(head: T, tail: List)

// Exercise (a): defining the size of a list (using natural numbers defined above)
/*
 * We are modelling the function as a recursive one.
 * The size of an empty list (Nil) is Zero.
 * 
 * The size of a non-empty list is the successor of the size of the list's tail.
 */
function Size(l: List<Nat>): Nat
    decreases l
{
    if l.Nil? then Zero else S(Size(l.tail))
}

// Exercise (b): defining the concatenation of two lists
/*
 * Concatenation with an empty list yields the other list.
 * 
 * The function recursively calculates the result of the concatenation.
 */
function Concatenation(l1: List<Nat>, l2: List<Nat>) : List<Nat>
    decreases l1
{
    match l1
        case Nil => l2
        case Append(head1, tail1) => Append(head1, Concatenation(tail1, l2))
}

// Exercise (c): proving that the size of the concatenation of two lists is the sum of the lists' sizes
/*
 * Starting with a base case in which the first list is empty, the proof is trivial, given ZeroAddNeutral.
 * Afterwards, the induction follows the next step and matches the second list.
 * If the list is empty, the result will be, of course, the first list.
 * Otherwise, an element is discarded from both (the heads), and the verification continues on the tails.
 */
lemma {:induction l1, l2} SizeOfConcatenationIsSumOfSizes(l1: List<Nat>, l2: List<Nat>)
    ensures Size(Concatenation(l1, l2)) == Add(Size(l1), Size(l2))
    decreases l1, l2
{
    match l1
        case Nil => {
            ZeroAddNeutral(Size(l2));
            assert Size(Concatenation(Nil, l2)) == Size(l2);
            assert Size(l2) == Add(Zero, Size(l2));
            assert Add(Zero, Size(l2)) == Add(Size(l1), Size(l2));
        }
        case Append(_, tail1) => {
            SizeOfConcatenationIsSumOfSizes(tail1, l2);
            assert Size(Concatenation(l1, l2)) == S(Size(Concatenation(tail1, l2)));
            assert S(Size(Concatenation(tail1, l2))) == S(Add(Size(tail1), Size(l2)));
            assert S(Add(Size(tail1), Size(l2))) == Add(S(Size(tail1)), Size(l2));
            assert Add(S(Size(tail1)), Size(l2)) == Add(Size(l1), Size(l2));
        }
}

// Exercise (d): defining a function reversing a list
/*
 * The base case is, again, the empty list. 
 * When the list is empty, the reverse of the list is also Nil.
 * 
 * When dealing with a non-empty list, we make use of the Concatenation operation.
 * The Reverse of the list will be a concatenation between the reverse of the tail and the head.
 * Since the head is not a list on its own, a list is created using the Append constructor.
 */
function ReverseList(l: List<Nat>) : List<Nat>
    decreases l
{
    if l.Nil? then Nil else Concatenation(ReverseList(l.tail), Append(l.head, Nil))
}

// Exercise (e): proving that reversing a list twice we obtain the initial list.
/*
 * Given that during the induction we need to make use of this property, 
 * we first save the result of reversing a concatenation between a list and a single element.
 *
 * Aside from the base case, proven with chained equality assertions, the proof follows an inductive approach as well.
 */
lemma {:induction l, n} ReversalOfConcatenationWithHead(l: List<Nat>, n: Nat)
    ensures ReverseList(Concatenation(l, Append(n, Nil))) == Append(n, ReverseList(l))
    decreases l
{
    match l
        case Nil => {
            assert ReverseList(Concatenation(Nil, Append(n, Nil))) == ReverseList(Append(n, Nil));
            assert ReverseList(Append(n, Nil)) == Concatenation(ReverseList(Nil), Append(n, Nil));
            assert Concatenation(ReverseList(Nil), Append(n, Nil)) == Concatenation(Nil, Append(n, Nil));
            assert Concatenation(Nil, Append(n, Nil)) == Append(n, Nil);
            assert Append(n, Nil) == Append(n, ReverseList(Nil));
        }
        case Append(head, tail) => {
            ReversalOfConcatenationWithHead(tail, n);
            assert ReverseList(Concatenation(l, Append(n, Nil))) == ReverseList(Concatenation(Append(head, tail), Append(n, Nil)));
            assert ReverseList(Concatenation(Append(head, tail), Append(n, Nil))) == Concatenation(ReverseList(Append(n, Nil)), ReverseList(Append(head, tail)));
            assert Concatenation(ReverseList(Append(n, Nil)), ReverseList(Append(head, tail))) == Concatenation(Append(n, Nil), Concatenation(ReverseList(tail), Append(head, Nil)));
            assert Concatenation(Append(n, Nil), Concatenation(ReverseList(tail), Append(head, Nil))) == Append(n, Concatenation(ReverseList(tail), Append(head, Nil)));
            assert Append(n, Concatenation(ReverseList(tail), Append(head, Nil))) == Append(n, ReverseList(l));
        }
}

/*
 * The induction starts with the base case, which is trivial.
 *
 * For the inductive steps, there is a need for the property proven above.
 * Once the property is guaranteed, the chained assertions lead to the solution.
 */
lemma {:induction l} DoubleReversalResultsInInitialList(l: List<Nat>)
    ensures l == ReverseList(ReverseList(l))
    decreases l
{
    match l
        case Nil => {
            assert ReverseList(ReverseList(Nil)) == ReverseList(Nil);
            assert ReverseList(Nil) == Nil;
        }
        case Append(head, tail) => {
            DoubleReversalResultsInInitialList(tail);
            ReversalOfConcatenationWithHead(ReverseList(tail), head);
            assert ReverseList(ReverseList(Append(head, tail))) == ReverseList(Concatenation(ReverseList(tail), Append(head, Nil)));
            assert ReverseList(Concatenation(ReverseList(tail), Append(head, Nil))) == Append(head, ReverseList(ReverseList(tail)));
            assert Append(head, ReverseList(ReverseList(tail))) == Append(head, tail);
            assert Append(head, tail) == l;
        }
}

The error message indicates a syntax error at line 318, which is the last line of the code. Upon reviewing the code, it appears that the error was caused by an incomplete comment at the en