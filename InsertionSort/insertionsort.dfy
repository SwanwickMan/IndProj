// List definition

datatype List<T> = | Nil | Cons(head: T, tail: List<T>)

// Define Ordered
predicate Ordered(xs: List<int>)
{
  match xs
  case Nil => true
  case Cons(_, Nil) => true
  case Cons(x, Cons(y, t)) => x <= y && Ordered(Cons(y, t))
}

// Count occurrences of value p in the list
function Project(xs: List<int>, p: int): nat
{
  match xs
  case Nil => 0
  case Cons(x, t) => (if x == p then 1 else 0) + Project(t, p)
}

// ---------- Insertion Sort ----------

function Insert(y: int, xs: List<int>): List<int>
{
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, t) =>
    if y < x then Cons(y, xs) else Cons(x, Insert(y, t))
}

function InsertionSort(xs: List<int>): List<int>
{
  match xs
  case Nil => Nil
  case Cons(x, t) => Insert(x, InsertionSort(t))
}

// ---------- Lemmas: orderedness ----------

// Insert preserves order when inserting into an ordered list
lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{
  // As discussed in the text, with the 'requires Ordered(xs)'
  // Dafny can discharge this automatically.
}

// InsertionSort returns an ordered list
lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
  decreases xs
{
  match xs
  case Nil => {}
  case Cons(x, t) =>
    InsertionSortOrdered(t);
    InsertOrdered(x, InsertionSort(t));
}

// ---------- Lemmas: same-elements property via Project (counts) ----------

// Inserting y changes the p-count exactly as Cons(y, xs) would
lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
  decreases xs
{
  // Automatic by unfolding Project/Insert
}

// InsertionSort preserves the count of any element p
lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
  decreases xs
{
  match xs
  case Nil => {}
  case Cons(x, t) =>
    InsertionSortSameElements(t, p);
    InsertSameElements(x, InsertionSort(t), p);
}

method Main()
{
  // unsorted list [5, 1, 9, 3, 7, 2, 4, 6]
  var lst := Cons(5,
              Cons(1,
              Cons(9,
              Cons(3,
              Cons(7,
              Cons(2,
              Cons(4,
              Cons(6, Nil))))))));

  print "Before: ", lst, "\n";

  var sorted := InsertionSort(lst);

  print "After:  ", sorted, "\n";
}
