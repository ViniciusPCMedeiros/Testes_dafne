ghost function Sum(n: nat):nat
{
  if n == 0
  then 0
  else n + Sum(n-1)
}

method ComputeSum(n:nat) returns (s:nat)
  ensures s == Sum(n)
{
    s := 0;
    var i := 0;
    while i < n
    invariant s == Sum(i)
    invariant 0 <= i <= n
    {
        i := i + 1;
        s := s + i;
    }
    }


function Ackerman(m: nat, n: nat):nat
    decreases m , n
{
  if m == 0
  then n + 1
  else if  n == 0
       then Ackerman(m-1, 1)
       else Ackerman(m-1, Ackerman(m, n-1))
}