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

method {:test} Test14() {
var r0 := Fatorial(109);
expect r0 == Fat(109);
}

// REPEAT 10 - TIME: 11.9254514 s
