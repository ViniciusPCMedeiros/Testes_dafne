ghost function Fib(n: nat):nat
{
  if n < 2
  then n
  else Fib(n-2) + Fib(n-1)
}

method ComputeFib(n:nat) returns (x:nat)
  ensures x == Fib(n)
{
  x:= 0;
  var y := 1;
  var i := 0;
  while i < n
    invariant x == Fib(i) && y == Fib(i+1) 
    invariant 0 <= i <= n
  {
    x, y := y, x + y;
    i := i + 1;
  }

}

