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

method {:test} Test7() {
var r0 := SquareRoot(10200);
expect r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 6.8983132 s
