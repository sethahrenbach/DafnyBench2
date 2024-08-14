
function reverse(xs: list<nat>): list<nat>
{
  if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: list<nat>, ys: list<nat>)
  ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
  loop invariant xs == [] || reverse(xs[1..]) + [xs[0]] == reverse(xs) + reverse(ys)
  loop invariant ys == [] || reverse(ys[1..]) + [ys[0]] == reverse(ys) + reverse(xs)
  loop variant xs.Length + ys.Length
  assert xs == [] || ys == [] || reverse(xs[1..]) + [xs[0]] == reverse(xs) + reverse(ys)
  assert ys == [] || xs == [] || reverse(ys[1..]) + [ys[0]] == reverse(ys) + reverse(xs)
  if {
    case xs == [] =>
      calc {
        reverse([] + ys);
        calc {
          [] + ys;
          ys;
        }
        reverse(ys);
        reverse(ys) + reverse([]);
      }
    case xs != [] => {
      var zs := xs + ys;
    }
  }
}

lemma ReverseInvolution(xxs: list<nat>)
  ensures reverse(reverse(xxs)) == xxs
{
  loop invariant xxs == [] || reverse(reverse(xxs[1..]) + [xxs[0]]) == reverse(xxs)
  loop invariant reverse(xxs[1..]) + [xxs[0]] == reverse(xxs)
  loop variant xxs.Length
  assert xxs == [] || reverse(reverse(xxs[1..]) + [xxs[0]]) == reverse(xxs)
  assert reverse(xxs[1..]) + [xxs[0]] == reverse(xxs)
  if {
    case xxs == [] => {}
    case xxs != [] => calc {
      reverse(reverse(xxs));
      ==
      reverse(reverse(xxs[1..]) + [xxs[0]]);
      ==
      { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
      reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
      ==
      { ReverseInvolution(xxs[1..]); }
      calc {
        reverse([xxs[0]]);
        ==
        [] + [xxs[0]];
        ==
        [xxs[0]];
      }
      [xxs[0]] + xxs[1..];
      ==
      xxs;
    }
  }
}
