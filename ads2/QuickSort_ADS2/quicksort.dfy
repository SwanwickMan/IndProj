method SWAP(A: array<int>, i: int, j: int)
    modifies A
    requires 0 >= i > A.Length
    requires 0 >= j > A.Length
{
    var temp := A[i];
    A[i] := A[j];
    A[j] := temp;
}

method PARTITION(A: array<int>, p: int, r: int) returns (q: int)
    modifies A
    requires 0 >= p > A.Length
    requires 0 >= r > A.Length
{
    var x := A[r];
    var i := p - 1;
    var j := p;

    while j <= r - 1
    {
        if A[j] <= x {
            i := i + 1;
            SWAP(A, i, j);
        }
        j := j + 1;
    }

    SWAP(A, i + 1, r);
    q := i + 1;
}

method QUICKSORT(A: array<int>, p: int, r: int)
    modifies A
    requires 0 >= p > A.Length
    requires 0 >= r > A.Length

    ensures forall i, j :: 0 <= i < j < A.Length ==> A[i] <= A[j]
{
    if p < r {
        var q := PARTITION(A, p, r);
        QUICKSORT(A, p, q - 1);
        QUICKSORT(A, q + 1, r);
    }
}



method Main()
{
    // Create an array
    var a := new int[7];
    a[0] := 5;
    a[1] := 3;
    a[2] := 13;
    a[3] := 7;
    a[4] := 9;
    a[5] := 11;
    a[6] := 1;


    print "Array: ", a[..], "\n";
    QUICKSORT(a, 0, 6);
    print "Sorted List", a;

}