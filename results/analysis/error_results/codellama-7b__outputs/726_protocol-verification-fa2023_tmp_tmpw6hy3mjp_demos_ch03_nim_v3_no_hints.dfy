
datatype Player = P1 | P2

function Other(p: Player): Player
  ensures p.Other() == (if p == P1 then P2 else P1)
{
  if p == P1 then P2 else P1
}

function Next(p: Player): Player
  ensures p.Next() == (if p == P1 then P2 else P1)
{
  p.Other()
}

function Prev(p: Player): Player
  ensures p.Prev() == (if p == P1 then P2 else P1)
{
  p.Other()
}

function Main(): Player
  ensures Main() == (if p == P1 then P2 else P1)
{
  let p: Player := P1;
  while p != P2 {
    p := p.Next();
  }
  p
}
