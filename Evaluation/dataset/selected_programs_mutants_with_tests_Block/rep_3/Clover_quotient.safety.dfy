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

method {:test} Test2() {
expect 7722 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(7722, 7722);
expect r1 * 7722 + r0 == 7722 && 0 <= r0 < 7722 && 0 <= r1;
}

// REPEAT 3 - TIME: 3.185171 s
