datatype IntList =
Nil
| Cons(head: int, tail: IntList)

function Length(l: IntList): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + Length(t)
}

function Contains(l: IntList, x: int): bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || Contains(t, x)
}

function RemoveNegatives(l: IntList): IntList
  ensures forall x :: Contains(RemoveNegatives(l), x) ==> x >= 0
  ensures Length(RemoveNegatives(l)) <= Length(l)
{
  match l
  case Nil => Nil
  case Cons(h, t) =>
    if h < 0 then
      RemoveNegatives(t)
    else
      Cons(h, RemoveNegatives(t))
}