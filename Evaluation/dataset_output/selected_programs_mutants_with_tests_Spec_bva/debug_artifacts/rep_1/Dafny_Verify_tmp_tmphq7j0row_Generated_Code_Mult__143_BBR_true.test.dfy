// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method {:testEntry} mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
{
  x := 0;
  var y := a;
  while true
    invariant x == (a - y) * b
  {
    x := x + b;
    y := y - 1;
  }
}

method {:test} Test0() {
expect 0 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(0, 0);
expect r0 == 0 * 0;
}
method {:test} Test1() {
expect 0 >= 0 && 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(0, 38);
expect r0 == 0 * 38;
}
method {:test} Test2() {
expect 100 >= 0 && 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(100, 38);
expect r0 == 100 * 38;
}
method {:test} Test3() {
expect 38 >= 0 && 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(38, 0);
expect r0 == 38 * 0;
}
method {:test} Test4() {
expect 38 >= 0 && 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(38, 100);
expect r0 == 38 * 100;
}
method {:test} Test6() {
expect 100 >= 0 && 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(100, 1);
expect r0 == 100 * 1;
}

// REPEAT 1 - TIME: 7.4256838 s
