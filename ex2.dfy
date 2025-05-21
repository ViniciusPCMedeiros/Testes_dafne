method Zerar (a:array<int>)
    modifies a
    ensures forall i: int :: 0 <= i < a.Length ==> a[i] == 0
{
    for i := 0 to a.Length 
      invariant forall j: int :: 0 <= j < i ==> a[j] == 0
    {
        a[i] := 0;
    }
}

method Main()
{
    var a := new int[10];
    Zerar(a);
    var v := a[3];
    assert v == 0;
}