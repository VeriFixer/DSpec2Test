// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_Mult.dfy

method {:testEntry} mult(a: int, b: int) returns (x: int)
  requires a >= 0 && b >= 0
  ensures x == a * b
{
  x := 0;
  var y := a;
  while y > 0
    invariant x == (a - y) * b
  {
    x := x * b;
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

// REPEAT 1 - TIME: 9.4718489 s

method {:test} Test9() {
expect 101 >= 0 && 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(101, 101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 10.6970226 s

method {:test} Test10() {
expect 102 >= 0 && 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(102, 102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 12.0426682 s

method {:test} Test11() {
expect 103 >= 0 && 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(103, 103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 13.2282914 s

method {:test} Test12() {
expect 104 >= 0 && 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(104, 104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 14.3580241 s

method {:test} Test13() {
expect 105 >= 0 && 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(105, 105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 15.4428214 s

method {:test} Test14() {
expect 106 >= 0 && 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(106, 106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 16.4027462 s

method {:test} Test15() {
expect 107 >= 0 && 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(107, 107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 17.2253647 s

method {:test} Test16() {
expect 108 >= 0 && 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(108, 108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 17.9617325 s

method {:test} Test17() {
expect 109 >= 0 && 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mult(109, 109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 18.6968357 s
