ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
 multiset(a) == multiset(b)
}
ghost predicate OrdenadoEntre(a:array<int>, e:int, d:int)
 requires 0 <= e <= d <= a.Length
 reads a
{
 forall i,j ::e <= i <= j < d ==> a[i] <= a[j]
}
ghost predicate Ordenado(a:array<int>)
 reads a
{
 OrdenadoEntre(a,0,a.Length)

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


method BubbleSort(a: array<int>)
    modifies a
    ensures Ordenado(a)
    ensures Permutacao(a[..], old(a[..]))
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    
{
    var n := a.Length;
    var i := 0;
    while i < n
        
    {       
        var swapped := false;
        var j := 0;
        while j < n - i - 1

            invariant Permutacao(a[..], old(a[..]))
            
            
        {
            
            if a[j] > a[j + 1] {
                a[j], a[j + 1] := a[j + 1], a[j];
                swapped := true;
            }
            j := j + 1;
        }
        if !swapped {
            break;
        }
        i := i + 1;
    }
}

     
method Main()
{
    var a := new int[] [3,0,7,-1,7];
    BubbleSort(a);
    assert a[..] == [-1,0,3,7,7];
}
