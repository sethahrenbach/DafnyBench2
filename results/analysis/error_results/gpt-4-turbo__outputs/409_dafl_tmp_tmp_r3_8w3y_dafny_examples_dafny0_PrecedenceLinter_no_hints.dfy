
// RUN: %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P0(A: bool, B: bool, C: bool) {
  A &&
  B ==> C // warning: suspicious lack of parentheses (lhs of ==>)
}

predicate P1(A: bool, B: bool, C: bool) {
  A && B ==>
    C
}

predicate P2(A: bool, B: bool, C: bool) {
  A &&
  B
  ==>
  C
}

predicate P3(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==>
  C &&
  D
}

predicate P4(A: bool, B: bool, C: bool, D: bool) {
    A &&
    B
  ==>
    C &&
    D
}

predicate P5(A: bool, B: bool, C: bool) {
  A ==>
  && B
  && C
}

predicate P6(A: bool, B: bool, C: bool) {
  A ==>
  || B
  || C
}

predicate Q0(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> C && // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
  D
}

predicate Q1(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> C && // warning: suspicious lack of parentheses (lhs of ==>)
        D
}

predicate Q2(A: bool, B: bool, C: bool, D: bool) {
  A &&
  B ==> (C && // warning: suspicious lack of parentheses (lhs of ==>)
  D)
}

predicate Q3(A: bool, B: bool, C: bool, D: bool) {
  (A &&
  B) ==> (C &&
  D)
}

predicate Q4(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> C // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
  && D
}

predicate Q4a(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    C && D
}

predicate Q4b(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    C &&
    D
}

predicate Q4c(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
  && C
  && D
}

predicate Q4d(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==>
    && C
    && D
}

predicate Q5(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> C // warning: suspicious lack of parentheses (lhs of ==>)
           && D
}

predicate Q6(A: bool, B: bool, C: bool, D: bool) {
  && A
  && B ==> && C // warning (x2): suspicious lack of parentheses (lhs and rhs of ==>)
           && D
}

predicate Q7(A: bool, B: bool, C: bool, D: bool) {
  A
  ==> // warning: suspicious lack of parentheses (rhs of ==>)
    B && C &&
  D
}

predicate Q8(A: bool, B: bool, C: bool, D: bool) {
  A
  ==>
    B && C &&
    D
}

predicate Q8a(A: bool, B: bool, C: bool, D: bool) {
  (A
  ==>
    B && C &&
    D
  ) &&
  (B || C)
}

predicate Q8b(A: bool, B: bool, C: bool, D: bool) {
    A &&
    B
  ==>
    B &&
    D
}

predicate Q9(A: bool, B: bool, C: bool) {
  A ==> B ==>
  C
}

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
    Q(x) &&
    R(x)
}

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) && Q(x) ==>
    R(x)
}

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) ==>
    R(x)
}

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
    Q(x) ==>
    R(x)
}

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==> Q(x) ==>
  R(x)
}

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: P(x) ==>
  forall y :: Q(y) ==>
  R(x)
}

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x :: (P(x) ==> Q(x)) && // warning: suspicious lack of parentheses (forall)
  R(x)
}

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x ::
  (P(x) ==> Q(x)) &&
  R(x)
}

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool) {
  forall x ::
    (P(x) ==> Q(x)) &&
    R(x)
}

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool) {
  exists x :: (P(x) ==> Q(x)) && // warning: suspicious lack of parentheses (exists)
  R(x)
}

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool) {
  exists x :: P(x) && // warning: suspicious lack of parentheses (exists)
  exists y :: Q(y) && // warning: suspicious lack of parentheses (exists)
  R(x)
}
