class Automaton {

  method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
    returns (table: seq<seq<bool>>)
    requires |init| >= 2
    ensures |table| == 1 + steps
    ensures table[0] == init
    ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
    ensures forall i | 0 <= i < |table| - 1 ::
              forall j | 1 <= j < |table[i]| - 1 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
    ensures forall i | 0 <= i < |table| - 1 ::
              table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
  {
    var result: seq<seq<bool>> := [init];
    var currentSeq := init;
    var index := 0;

    while index < steps
      invariant |result| == index + 1
      invariant result[0] == init
      invariant forall i | 0 <= i < |result| :: |result[i]| == |init|
      invariant forall i | 0 <= i < index ::
                  forall j | 1 <= j < |result[i]| - 1 :: result[i + 1][j] == rule(result[i][j - 1], result[i][j], result[i][j + 1])
      invariant forall i | 0 <= i < index ::
                  result[i + 1][0] == rule(false, result[i][0], result[i][1]) && result[i + 1][|result[i]| - 1] == rule(result[i][|result[i]| - 2], result[i][|result[i]| - 1], false)
      decreases steps - index
    {
      var nextSeq := [rule(false, currentSeq[0], currentSeq[1])];
      var index2 := 1;

      while index2 < |currentSeq| - 1
        invariant 1 <= index2 < |currentSeq| - 1
        invariant |nextSeq| == index2
        invariant forall j | 1 <= j < index2 :: nextSeq[j] == rule(currentSeq[j - 1], currentSeq[j], currentSeq[j + 1])
        decreases |currentSeq| - index2
      {
        nextSeq := nextSeq + [rule(currentSeq[index2 - 1], currentSeq[index2], currentSeq[index2 + 1])];
        index2 := index2 + 1;
      }
      nextSeq := nextSeq + [rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false)];

      currentSeq := nextSeq;
      result := result + [nextSeq];
      index := index + 1;
    }

    return result;
  }

  function TheRule(a: bool, b: bool, c: bool): bool
  {
    a || b || c
  }

  function TheRule2(a: bool, b: bool, c: bool): bool
  {
    a && b && c
  }

  method testMethod() {
    var init := [false, false, true, false, false];
    var result := ExecuteAutomaton(init, TheRule, 3);
    var result2 := ExecuteAutomaton(init, TheRule2, 2);
  }
}