method CountingSort(A: array<int>, B: array<int>, k: int)
    requires A != null && B != null
    requires A.Length == B.Length
    requires k >= 0
    requires forall i :: 0 <= i < A.Length ==> 0 <= A[i] <= k
    modifies B
    ensures multiset(B[..]) == multiset(A[..])
    ensures forall i, j :: 0 <= i < j < B.Length ==> B[i] <= B[j]
{
    var n := A.Length;

    // Step 1: initialize array C[0..k] with zeros
    var C := new int[k + 1];
    assert forall x :: 0 <= x <= k ==> C[x] == 0;
    // Dafny arrays are initialized to zero by default

    // Step 2: count each element in A
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant forall x :: 0 <= x <= k ==> C[x] >= 0
        invariant forall x :: 0 <= x <= k ==> 
            C[x] == |multiset(A[..j]) * multiset([x])|
    {
        C[A[j]] := C[A[j]] + 1;
        j := j + 1;
    }

    // Step 3: accumulate counts
    var i := 1;
    while i <= k
        invariant 1 <= i <= k + 1
        invariant forall x :: 0 <= x < i ==> C[x] >= 0
        invariant forall x :: 1 <= x < i ==> C[x] >= C[x - 1]
        invariant forall x :: 0 <= x <= k ==> C[x] >= 0
        decreases k - i + 1
    {
        C[i] := C[i] + C[i - 1];
        i := i + 1;
    }

    // Step 4: fill B from A in reverse order (stable sort)
    j := n - 1;
    while j >= 0
        invariant -1 <= j < n
        invariant forall idx :: j < idx < n ==> 0 <= B[idx] <= k
        invariant multiset(B[j+1..]) == multiset(A[j+1..])
        invariant forall x :: 0 <= x <= k ==> C[x] >= 0
        decreases j + 1
    {
        var a_j := A[j];
        var pos := C[a_j] - 1;
        B[pos] := a_j;
        C[a_j] := C[a_j] - 1;
        j := j - 1;
    }

    // Postconditions:
    // - B is sorted
    // - B is a permutation of A
}
