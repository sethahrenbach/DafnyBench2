
module Rope {
  class Rope {
    ghost var Contents: string;
    ghost var Repr: set<Rope>;

    var data: string;
    var weight: nat;
    var left: Rope?;
    var right: Rope?;

    ghost predicate Valid() 
        reads this, Repr
        ensures Valid() ==> this in Repr
    {
        this in Repr &&
        (left != null ==> 
            left in Repr &&
            left.Repr < Repr && this !in left.Repr &&
            left.Valid() &&
            (forall child :: child in left.Repr ==> child.weight <= weight)) &&
        (right != null ==> 
            right in Repr &&
            right.Repr < Repr && this !in right.Repr &&
            right.Valid()) &&
        (left == null && right == null ==>
            Repr == {this} &&
            Contents == data &&
            weight == |data| &&
            data != "") &&
        (left != null && right == null ==>
            Repr == {this} + left.Repr &&
            Contents == left.Contents &&
            weight == |left.Contents| &&
            data == "") &&
        (left == null && right != null ==>
            Repr == {this} + right.Repr &&
            Contents == right.Contents &&
            weight == 0 &&
            data == "") &&
        (left != null && right != null ==>
            Repr == {this} + left.Repr + right.Repr &&
            left.Repr !! right.Repr &&
            Contents == left.Contents + right.Contents &&
            weight == |left.Contents| &&
            data == "") 
    }

    lemma contentSizeGtZero()
        requires Valid()
        ensures |Contents| > 0
    {
        assert Contents != "";
    }

    function getWeightsOfAllRightChildren(): nat
        reads right, Repr
        requires Valid()
        ensures right != null ==> getWeightsOfAllRightChildren() == |right.Contents|
    {
        if right == null then 0
        else right.weight + right.getWeightsOfAllRightChildren()
    } 

    function length(): nat
        reads Repr
        requires Valid()
        ensures |Contents| == length()
    {
        this.weight + getWeightsOfAllRightChildren()
    }

    constructor Terminal(x: string)
        requires x != ""
        ensures Valid() && fresh(Repr) && left == null && right == null && data == x
    { 
        data := x;
        weight := |x|;
        left := null;
        right := null;
        Contents := x;
        Repr := {this};
    }   

    predicate isTerminal()
        reads this, this.left, this.right
    { left == null && right == null }

    method report(i: nat, j: nat) returns (s: string)
        requires 0 <= i <= j <= |this.Contents|
        requires Valid()
        ensures s == this.Contents[i..j]
    {
        if i == j {
            s := "";
        } else {
            if this.left == null && this.right == null {
                s := data[i..j];
            } else {
                if (j <= this.weight) {
                    s := this.left.report(i, j);
                } else if (this.weight <= i) {
                    s := this.right.report(i - this.weight, j - this.weight);
                } else {
                    var s1 := this.left.report(i, this.weight);
                    var s2 := this.right.report(0, j - this.weight);
                    s := s1 + s2;
                }
            }
        }
    }

    method toString() returns (s: string)
        requires Valid()
        ensures s == Contents
    {
        s := report(0, this.length());
    }

    method getCharAtIndex(index: nat) returns (c: char)
        requires Valid() && 0 <= index < |Contents|
        ensures c == Contents[index]
    {
        var nTemp := this;
        var i := index;
        while (!nTemp.isTerminal()) 
        {
            invariant nTemp != null && nTemp.Valid() && 0 <= i < |nTemp.Contents|;
            if (i < nTemp.weight) {
                nTemp := nTemp.left;
            } else {
                i := i - nTemp.weight;
                nTemp := nTemp.right;
            }
        }
        c := nTemp.data[i];
    }
  }
}
