method Zerado(n:nat) returns (a:array<int>)
    requires n > 0
    ensures a.Length == n && forall i: int :: 0 <= i < n ==> a[i] == 0
    ensures fresh(a)
{
    a := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j: int :: 0 <= j < i ==> a[j] == 0
    {
        a[i] := 0;
        i := i + 1;
    }
}
method Main()
{
    var a := Zerado(10);
    a[0] := 1;
}