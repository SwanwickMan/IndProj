method SelectionSort(a: array<int>)
  modifies a
  // Fully sorted on return
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Same multiset of elements as on entry
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  // Snapshot the initial multiset to avoid carrying `old(...)` through the loop.
  ghost var initial := multiset(a[..]);

  var n := 0;

  while n != a.Length
    invariant 0 <= n <= a.Length
    // The first n elements are sorted (non-decreasing)
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    // Every element in the sorted prefix is <= any element in the unsorted suffix
    invariant SplitPoint(a, n)
    // The array contents (as a bag) stay the same as at entry
    invariant multiset(a[..]) == initial
    decreases a.Length - n
  {
    var mindex, m := n, n + 1;

    while m != a.Length
      // Keep mindex inside the scanned window [n, m)
      invariant n <= mindex < m <= a.Length
      // a[mindex] is the minimum among a[n..m)
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      // Outer invariants that the inner loop should not break
      invariant 0 <= n <= a.Length
      invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
      invariant SplitPoint(a, n)
      // Multiset stays unchanged (inner loop doesn’t mutate the array)
      invariant multiset(a[..]) == initial
      decreases a.Length - m
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }

    a[n], a[mindex] := a[mindex], a[n];

    // After swapping, the multiset is unchanged (swap is a permutation)
    assert multiset(a[..]) == initial;

    n := n + 1;
  }
}

// Elements before n are sorted and also <= any element at/after n
ghost predicate SplitPoint(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}


// ---------------------- Demo ----------------------

method Main()
{
  var a := new int[8];
  a[0] := 5;
  a[1] := 1;
  a[2] := 9;
  a[3] := 3;
  a[4] := 7;
  a[5] := 2;
  a[6] := 4;
  a[7] := 6;

  print "Before: ", a[..], "\n";
  SelectionSort(a);
  print "After:  ", a[..], "\n";
}