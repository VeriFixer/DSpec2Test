method {:testEntry} Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r:=x;
  q:=0;
  while y<=r
    invariant q*y+r==x && r>=0
    decreases r
  {
    r:=r-y;
    q:=q+1;

  }
}

method {:test} Test19() {
expect 246339 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246338, 246339);
expect r1 * 246339 + r0 == 246338 && 0 <= r0 < 246339 && 0 <= r1;
}

// REPEAT 10 - TIME: 14.9891401 s
