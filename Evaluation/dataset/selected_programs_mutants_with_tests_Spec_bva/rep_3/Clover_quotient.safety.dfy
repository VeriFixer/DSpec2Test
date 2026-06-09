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

method {:test} Test12() {
expect 246332 != 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := Quotient(246331, 246332);
expect r1 * 246332 + r0 == 246331 && 0 <= r0 < 246332 && 0 <= r1;
}

// REPEAT 3 - TIME: 8.5327385 s
