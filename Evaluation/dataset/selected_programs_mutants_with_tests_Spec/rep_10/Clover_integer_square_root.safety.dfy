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

method {:test} Test9() {
var r0 := SquareRoot(35);
expect r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 10.0918789 s
