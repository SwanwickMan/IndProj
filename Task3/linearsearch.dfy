method LinearSearch(a: array<int>, key: int) returns (index: int)
    // Task to include the postconditions

{
    index := 0;

    while index < a.Length
        //Task to include both invariants
        
    {
        if a[index] == key {
            return;
        }

        index := index + 1;
    }
}