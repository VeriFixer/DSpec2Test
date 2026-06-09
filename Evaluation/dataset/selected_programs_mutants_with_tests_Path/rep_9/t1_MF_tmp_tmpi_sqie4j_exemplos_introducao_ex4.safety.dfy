function Fat(n: nat): nat
{
   if n == 0 then 1 else n * Fat(n-1)
}

method {:testEntry} Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
    r := 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == Fat(i)
    {
        i := i + 1;
        r := r * i;
    }
}

method {:test} Test8() {
var r0 := Fatorial(10);
expect r0 == Fat(10);
}

// REPEAT 9 - TIME: 20.2180365 s
