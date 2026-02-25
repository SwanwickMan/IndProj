// Helper predicate to check if an array segment is sorted
predicate isSorted(a: array<int>, lo: int, hi: int)
    reads a
    requires 0 <= lo <= hi <= a.Length
{
    forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

method MERGE(A: array<int>, p: int, q: int, r: int)
    modifies A
    requires 0 <= p <= q < r <= A.Length
    requires isSorted(A, p, q + 1)
    requires isSorted(A, q + 1, r)
    ensures isSorted(A, p, r)
    ensures multiset(A[p..r]) == multiset(old(A[p..r]))
    ensures forall i :: 0 <= i < p || r <= i < A.Length ==> A[i] == old(A[i])
{
    var n1 := q - p + 1;
    var n2 := r - (q + 1);

    // Create temporary copies of the two halves
    var L := new int[n1];
    var R := new int[n2];

    forall i | 0 <= i < n1 { L[i] := A[p + i]; }
    forall j | 0 <= j < n2 { R[j] := A[q + 1 + j]; }

    var i, j, k := 0, 0, p;

    while k < r
        invariant p <= k <= r
        invariant 0 <= i <= n1 && 0 <= j <= n2
        invariant k == p + i + j
        invariant isSorted(A, p, k)
        // Ensure A[p..k] contains only elements from L[0..i] and R[0..j]
        invariant multiset(A[p..k]) == multiset(L[..i]) + multiset(R[..j])
        // The elements in the remainder of L and R are >= everything already in A[p..k]
        invariant forall m, n :: p <= m < k && i <= n < n1 ==> A[m] <= L[n]
        invariant forall m, n :: p <= m < k && j <= n < n2 ==> A[m] <= R[n]
    {
        if i < n1 && (j == n2 || L[i] <= R[j]) {
            A[k] := L[i];
            i := i + 1;
        } else {
            A[k] := R[j];
            j := j + 1;
        }
        k := k + 1;
    }
}

method MERGE_SORT(A: array<int>, p: int, r: int)
    modifies A
    requires 0 <= p <= r <= A.Length
    decreases r - p
    ensures isSorted(A, p, r)
    ensures multiset(A[p..r]) == multiset(old(A[p..r]))
{
    if r - p > 1 {
        var q := p + (r - p) / 2;
        
        // Correct recursive calls
        MERGE_SORT(A, p, q);
        MERGE_SORT(A, q, r);
        
        // Merge the results
        // Note: Using q-1 to match the p, q, r logic of the MERGE method
        MERGE(A, p, q - 1, r);
    }
}