// Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Square.dfy

method {:testEntry} square(n: int) returns (r: int)
  requires 0 <= n
  ensures r == n * n
{
  var x: int;
  var i: int;
  r := 0;
  i := 0;
  x := 1;
  while i < n
    invariant i <= n
    invariant r == i * i
    invariant x == 2 * i + 1
  {
    x := x + 2;
    i := i + 1;
  }
}


method {:test} Test0() {
expect 0 <= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(0);
expect r0 == 0 * 0;
}
method {:test} Test2() {
expect 0 <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 0 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 6.2629372 s

method {:test} Test7() {
expect 0 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 7.0918318 s

method {:test} Test8() {
expect 0 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 7.7963594 s

method {:test} Test9() {
expect 0 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 8.552287 s

method {:test} Test10() {
expect 0 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 9.2372999 s

method {:test} Test11() {
expect 0 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 9.9631747 s

method {:test} Test12() {
expect 0 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 10.7049296 s

method {:test} Test13() {
expect 0 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 11.5069595 s

method {:test} Test14() {
expect 0 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 12.2761492 s

method {:test} Test15() {
expect 0 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := square(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 12.9490154 s
