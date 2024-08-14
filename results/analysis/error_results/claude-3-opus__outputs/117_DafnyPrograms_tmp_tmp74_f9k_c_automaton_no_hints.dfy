/**
Consider cellular automata: a row of cells is repeatedly updated according to a rule. In this exercise I dabbled with,
each cell has the value either false or true. Each cell's next state depends only on the immediate neighbours, in the 
case where the cell is at the edges of the row, the inexistent neighbours are replaced by "false". The automaton table 
will contain the initial row, plus a row for each number of steps.
 */
class Automaton {

/**
This method computes the automaton.
Provide the initial row: init, the rule and the desired number of steps
 */
method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)
  requires |init| >= 2
  ensures |table| == 1 + steps
  ensures table[0] == init;
  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
{
  var result : seq<seq<bool>> := [init];
  var currentSeq := init;
  var index := 0;

  while index < steps
    invariant 0 <= index <= steps
    invariant |result| == index + 1
    invariant result[0] == init
    invariant forall i | 0 <= i < |result| :: |result[i]| == |init|
    invariant currentSeq == result[index]
    invariant forall i | 0 <= i < index ::
                forall j | 1 <= j <= |result[i]| - 2 :: result[i + 1][j] == rule(result[i][j - 1], result[i][j], result[i][j + 1])
    invariant forall i | 0 <= i < index ::
                result[i + 1][0] == rule(false, result[i][0], result[i][1]) && result[i + 1][|result[i]| - 1] == rule(result[i][|result[i]| - 2], result[i][|result[i]| - 1], false)
    decreases steps - index
  {
    var index2 := 1;
    var nextSeq := [];
    nextSeq := nextSeq + [rule(false, currentSeq[0], currentSeq[1])];

    while index2 < |currentSeq| - 1
      invariant 1 <= index2 <= |currentSeq| - 1
      invariant |nextSeq| == index2
      invariant forall i | 0 <= i < index2 :: nextSeq[i] == if i == 0 then rule(false, currentSeq[0], currentSeq[1]) else rule(currentSeq[i-1], currentSeq[i], currentSeq[i+1])
      decreases |currentSeq| - 1 - index2
    {
      nextSeq := nextSeq + [rule(currentSeq[index2 - 1], currentSeq[index2], currentSeq[index2 + 1])];
      index2 := index2 + 1;
    }
    nextSeq := nextSeq + [rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false)];
    assert |nextSeq| == |currentSeq|;

    forall j | 1 <= j <= |nextSeq| - 2 
      ensures nextSeq[j] == rule(currentSeq[j - 1], currentSeq[j], currentSeq[j + 1])
    {
      assert 0 < j < |nextSeq| - 1;
      if j == 1 {
        assert nextSeq[1] == rule(currentSeq[0], currentSeq[1], currentSeq[2]);
      } else if j == |nextSeq| - 2 {
        assert nextSeq[|nextSeq| - 2] == rule(currentSeq[|nextSeq| - 3], currentSeq[|nextSeq| - 2], currentSeq[|nextSeq| - 1]);
      } else {
        assert 1 < j < |nextSeq| - 2;
        assert nextSeq[j] == rule(currentSeq[j - 1], currentSeq[j], currentSeq[j + 1]);
      }
    }
    assert nextSeq[0] == rule(false, currentSeq[0], currentSeq[1]) by {
      assert nextSeq[0] == rule(false, currentSeq[0], currentSeq[1]);
    }
    assert nextSeq[|nextSeq| - 1] == rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false);

    currentSeq := nextSeq;
    result := result + [nextSeq];
    index := index + 1;
  }

  return result;
}

// example rule
function TheRule(a: bool, b: bool, c: bool) : bool
{
  a || b || c
}

// example rule 2
function TheRule2(a: bool, b: bool, c: bool) : bool
{
  a && b && c
}

method testMethod() {
  var init := [false, false, true, false, false];

  var result := ExecuteAutomaton(init, TheRule, 3);
  
  var result2 := ExecuteAutomaton(init, TheRule2, 2);
}
}