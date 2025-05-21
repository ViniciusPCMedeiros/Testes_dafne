method FazAlgo(a: array<int>, n: int, e: int)
 requires 0 <= n < a.Length
 modifies a
 ensures multiset(a[..n+1]) == multiset(a[..n]) + multiset{e}
{
 a[n] := e;
 assert a[..n+1] == a[..n] + [e];

}

method TrocaElementos(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
    ensures forall k: int :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k])
    ensures a[i] == old(a[j]) && a[j] == old(a[i])
    {
        var temp := a[i];
        a[i] := a[j];
        a[j] := temp;
    } 


method Main()
{
    var a := new int[] [1,2,3,4,5];
    TrocaElementos(a, 0, 3);
    assert a[..] == [4,2,3,1,5];
    
    
}