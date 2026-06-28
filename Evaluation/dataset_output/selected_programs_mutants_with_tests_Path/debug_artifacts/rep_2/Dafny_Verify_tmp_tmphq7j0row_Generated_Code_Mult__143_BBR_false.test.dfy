// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method {:testEntry} mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
{
  x := 0;
  var y := a;
  while false
    invariant x == (a - y) * b
  {
    x := x + b;
    y := y - 1;
  }
}

method {:test} Test1() {
expect 1 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(1, 1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 12.3530288 s
