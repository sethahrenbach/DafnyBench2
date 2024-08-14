
function bulls_cows(secret: seq<nat>, guess: seq<nat>): (nat, nat)
  requires 0 <= |secret| <= 10
  requires 0 <= |guess| <= 10
  requires |secret| == |guess|
  ensures 0 <= result.0 <= |secret|
  ensures 0 <= result.1 <= |secret|
{
  var bulls: nat := 0;
  var cows: nat := 0;

  for i in 0..|secret| {
    if secret[i] == guess[i] {
      bulls := bulls + 1;
    } else if secret[i] in guess {
      cows := cows + 1;
    }
  }

  return (bulls, cows);
}
