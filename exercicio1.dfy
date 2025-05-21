method FindMaxIndex(a:array<int>) returns (i:int)
    requires a.Length > 0
    ensures 0 <= i < a.Length
    ensures forall j: int :: 0 <= j < a.Length ==> a[j] <= a[i]

{
    i := 0;
    for index := 0 to a.Length
        invariant 0 <= i < a.Length
        invariant forall j: int :: 0 <= j < index ==> a[j] <= a[i]
    {
    
        if a[index] > a[i] {
            i := index;
        }
    }
}

method FindMaxValue(a:array<int>) returns (m:int)
    requires a.Length > 0
    ensures exists i: int :: 0 <= i < a.Length && a[i] == m
    ensures forall j: int :: 0 <= j < a.Length ==> a[j] <= m


{
    for index := 0 to a.Length
        invariant 0 <= index < a.Length
        invariant forall j: int :: 0 <= j < index ==> a[j] <= m
    {
        if a[index] > m {
            m := a[index];
        }
    }
}

method Main()
{
    var a := new int[] [3,0,7,-1,7];
    var i := FindMaxIndex(a);
    assert a[i] == 7;   
    var m:= FindMaxValue(a);
    assert m == 7;
}