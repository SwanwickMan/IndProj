method SmallestDivisor(n: nat) returns (d: int)
  // Task to include the postconditions
{
  d := 2;
  while n % d != 0
    //Task to include both invariants
  {
    d := d + 1;
  }
}

method Main()
{
    var divisor := SmallestDivisor(9);
    print divisor;
}