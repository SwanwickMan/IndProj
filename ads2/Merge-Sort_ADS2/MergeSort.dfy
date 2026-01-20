method MakeCopyWithInfinity(A: array<int>, p: int, q: int) returns (L: array<int>)
    requires A != null
    requires 0 <= p <= q < A.Length
    ensures L.Length == (q - p + 2)        // +1 sentinel slot
    ensures forall i :: 0 <= i <= q - p ==> L[i] == A[p + i]
{
    var n1 := q - p + 1;

    // allocate new array with one extra element for sentinel
    L := new int[n1 + 1];

    // copy A[p..q] into L[0..n1-1]
    var i := 0;
    while i < n1
        invariant 0 <= i <= n1
        invariant forall k :: 0 <= k < i ==> L[k] == A[p + k]
    {
        L[i] := A[p + i];
        i := i + 1;
    }
    L[n1] := int.Max;
}



method MERGE(A: array<int>, p: int, q: int, r: int){
    var n1 := q - p + 1;
    var n2 := r - q;
    
    var L := copy(A, p, q);
    var R := copy(A, q + 1, r);

    L[n1] := int.Max
    R[n1] := int.Max


}



method MERGE_SORT(A: array<int>, p: int,r: int){
    if p < r{
        var q := (p+r)/2;
        MERGE_SORT(A,p,r);
        MERGE_SORT(A,q+1,r);
        MERGE(A,p,q,r);
    }
}