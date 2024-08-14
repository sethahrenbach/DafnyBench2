function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then pow(base * base, exponent / 2)
  else base * pow(base, exponent - 1)
}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
  result := operands[0];
  var i := 0;
  while i < |operators|
    invariant 0 <= i <= |operators|
    invariant |operators[..i]| + 1 == |operands[..i+1]|
    invariant forall j :: 0 <= j < i+1 ==> operands[j] >= 0
    invariant result >= 0
    invariant result == evaluate(operators[..i], operands[..i+1])
  {
    var op := operators[i];
    i := i + 1;
    match op
    {
      case '+' =>
        result := result + operands[i];
      case '-' =>
        if result >= operands[i] {
          result := result - operands[i];
        } else {
          result := 0;
        }
      case '*' =>
        result := result * operands[i];
      case '/' => 
        if operands[i] != 0 {
            result := result / operands[i];
        }
      case '^' => 
        result := pow(result, operands[i]);
      case _ =>
    }
  }
}

// Helper function to evaluate the expression
function evaluate(operators: seq<char>, operands: seq<int>): int
  requires |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
  ensures evaluate(operators, operands) >= 0
  decreases |operators|
{
  if |operators| == 0 then operands[0]
  else 
    var op := operators[0];
    var left := operands[0];
    var right := evaluate(operators[1..], operands[1..]);
    match op
    {
      case '+' => left + right
      case '-' => if left >= right then left - right else 0
      case '*' => left * right
      case '/' => if right != 0 then left / right else left
      case '^' => pow(left, right)
      case _ => left
    }
}