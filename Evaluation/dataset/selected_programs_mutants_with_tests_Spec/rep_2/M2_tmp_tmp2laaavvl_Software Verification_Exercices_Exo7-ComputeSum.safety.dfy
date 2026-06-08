function Sum(n:nat):nat
 
{
  if n==0 then  0 else n + Sum(n-1)
}

method {:testEntry} ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
{
    s := 0;
    var i := 0;
    while i< n
      invariant 0 <= i <= n
      invariant s == Sum(i)
      {
        s := s + i + 1;
        i := i+1;
      }
}

method {:test} Test1() {
var r0 := ComputeSum(7722);
expect r0 == Sum(7722);
}

// REPEAT 2 - TIME: 4.136106 s
