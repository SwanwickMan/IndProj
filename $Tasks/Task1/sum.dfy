method SumUpTo(n: int) returns (s: int)
    // Precondition: n must be non-negative
    requires n >= 0

    // Postcondition: the result s is equal to 1 + 2 + ... + n
    // using the closed form n*(n+1)/2
    ensures s == n * (n + 1) / 2
{
    var i := 0;
    s := 0;

    while i < n
        // Loop invariants:
        invariant 0 <= i <= n
        invariant s == i * (i + 1) / 2
    {
        i := i + 1;
        s := s + i;
    }
}
