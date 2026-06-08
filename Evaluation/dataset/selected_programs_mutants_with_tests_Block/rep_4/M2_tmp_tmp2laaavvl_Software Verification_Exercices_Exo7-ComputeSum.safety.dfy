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

method {:test} Test3() {
var r0 := ComputeSum(4);
expect r0 == Sum(4);
}

// REPEAT 4 - TIME: 4.1656977 s
