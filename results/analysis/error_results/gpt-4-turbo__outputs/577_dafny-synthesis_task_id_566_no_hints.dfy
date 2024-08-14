method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{
  sum := 0;
  var n: nat := number;

  ghost var ndigits := NumberOfDigits(number);
  X(number);

  ghost var PowersOfTen := seq(ndigits+1, i => Power10(i));
  ghost var pmax := Power10(ndigits);
  ghost var p := PowersOfTen[0];

  ghost var ValuesOfn := seq(ndigits+1, i => number / PowersOfTen[i]);

  ghost var i := 0;
  while n > 0
    invariant sum + SumDigits(n) == SumDigits(number)
    invariant n == number / Power10(i)
    invariant i <= ndigits
    invariant p == Power10(i)
    invariant forall k :: 0 <= k < i ==> ValuesOfn[k] == number / PowersOfTen[k]
  {
    var digit := n % 10;
    sum := sum + digit;
    n := n / 10;
    i := i + 1;
    p := PowersOfTen[i];
  }
  NumberIdentity(number, pmax);
}

lemma X(x: nat)
  ensures Power10(NumberOfDigits(x)) > x
{
  if x <= 9
  {
  }
  else
  {
    X(x/10);
  }
}

lemma NumberIdentity(number: nat, pmax: nat)
  requires pmax == Power10(NumberOfDigits(number))
  ensures number == number % pmax
{
  if NumberOfDigits(number) == 1
  {
  }
  else
  {
    NumberIdentity(number/10, pmax/10);
  }
}

function Power10(n: nat): (r: nat)
  ensures r >= 1
  ensures n > 0 ==> r % 10 == 0
{
  if (n == 0) then 1 else 10 * Power10(n-1)
}

function SumDigits(n: nat) : nat
{
  var digits := NumberToSeq(n);
  Sum(digits)
}

function NumberToSeq(number: nat) : seq<nat>
  requires number >= 0
{
  if number == 0 then []
  else [number % 10] + NumberToSeq(number/10)
}

function Sum(digits: seq<nat>) : nat
{
  if |digits| == 0 then 0 else digits[0] + Sum(digits[1..])
}

function NumberOfDigits(n: nat) : (r: nat)
  ensures r >= 1
  ensures r == 1 <==> 0 <= n <= 9
{
  if 0 <= n <= 9 then 1 else 1+NumberOfDigits(n/10)
}