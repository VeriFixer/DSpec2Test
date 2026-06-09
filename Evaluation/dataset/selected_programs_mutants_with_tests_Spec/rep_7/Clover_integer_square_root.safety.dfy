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

method {:test} Test6() {
var r0 := SquareRoot(24);
expect r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 6.9489478 s
