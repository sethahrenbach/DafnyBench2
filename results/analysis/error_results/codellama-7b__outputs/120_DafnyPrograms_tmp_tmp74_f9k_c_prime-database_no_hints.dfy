
method InsertNumber(n: nat)
  modifies database
  ensures n in database
  ensures database[n] == true
{
  var prime : bool;
  prime := testPrimeness(n);
  database := database[n := prime];
}
