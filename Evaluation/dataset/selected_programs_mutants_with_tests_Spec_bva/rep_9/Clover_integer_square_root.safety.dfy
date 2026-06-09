method {:testEntry} SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  r:=0;
  while (r+1)*(r+1)<=N
    invariant r*r<=N
  {
    r:=r+1;
  }
}

method {:test} Test13() {
var r0 := SquareRoot(10818);
expect r0 * r0 <= 10818 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 11.0455095 s
