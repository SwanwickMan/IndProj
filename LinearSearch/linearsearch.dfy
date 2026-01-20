method LinearSearch(a: array<int>, key: int) returns (index: int)
    // value must exist within the  list or return a.length
    ensures 0 <= index <= a.Length
    // if index is less than a.length then a[index] is our key
    ensures index < a.Length ==> a[index] == key
    // if index == a.length then key is not in the array
    ensures index == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
    index := 0;

    while index < a.Length
        //Task to include both invariants
        invariant 0 <= index <= a.Length
        invariant forall i :: 0 <= i < index ==> a[i] != key
    {
        if a[index] == key {
            return;
        }

        index := index + 1;
    }
}