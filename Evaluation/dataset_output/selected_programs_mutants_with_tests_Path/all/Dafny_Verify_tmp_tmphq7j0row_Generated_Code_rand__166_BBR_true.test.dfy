// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy

method {:testEntry} Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x * y;
  while true
    invariant x >= 0
    invariant z == x * y
    decreases x
  {
    x := x - 1;
    z := z - y;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(0, 0);
expect r0 == 0;
}

// REPEAT 1 - TIME: 7.2760327 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(1, 1);
expect r0 == 0;
}

// REPEAT 2 - TIME: 11.6674348 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(2, 2);
expect r0 == 0;
}

// REPEAT 3 - TIME: 14.9743901 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(3, 3);
expect r0 == 0;
}

// REPEAT 4 - TIME: 18.9009772 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(4, 4);
expect r0 == 0;
}

// REPEAT 5 - TIME: 22.568743 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(5, 5);
expect r0 == 0;
}

// REPEAT 6 - TIME: 26.3789789 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(6, 6);
expect r0 == 0;
}

// REPEAT 7 - TIME: 30.3781149 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(7, 7);
expect r0 == 0;
}

// REPEAT 8 - TIME: 34.405304 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(8, 8);
expect r0 == 0;
}

// REPEAT 9 - TIME: 39.2748011 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(9, 9);
expect r0 == 0;
}

// REPEAT 10 - TIME: 43.6071341 s
