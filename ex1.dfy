ghost function SomaAte(a:array<nat>, n:nat):nat
    decreases n
    requires n <= a.Length
    reads a
{
    if n == 0
    then 0
    else a[n-1] + SomaAte(a, n-1)
}

method Somatorio(a:array<nat>, n:nat) returns (s:nat)
    ensures s == SomaAte(a, a.Length)
{
    s := 0;
    var i := 0;
    while i < n
     decreases a.Length
     invariant 0 <= i <= a.Length
    invariant s == SomaAte(a, i)
    {
        s := s + a[i];
        i := i + 1;
    }
}