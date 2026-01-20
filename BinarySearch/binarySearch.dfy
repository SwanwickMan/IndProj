method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures 0 <= n <= a.Length
    ensures forall i :: 0 <= i < n ==> a[i] < key
    ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
    var lo, hi := 0, a.Length;

    while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> key <= a[i]
    decreases hi - lo
    invariant lo < hi ==> lo <= (lo + hi) / 2 < hi
    {
        var mid := (lo + hi) / 2;
        if a[mid] < key {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }

    n := lo;
}

method Main()
{
    // Create a sorted array
    var a := new int[7];
    a[0] := 1;
    a[1] := 3;
    a[2] := 5;
    a[3] := 7;
    a[4] := 9;
    a[5] := 11;
    a[6] := 13;
    // item from array
    var item := 5;


    print "Array: ", a[..], "\n";
    var foundIndex := BinarySearch(a, item);
    print item, " is at index ", foundIndex;

}