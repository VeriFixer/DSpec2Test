// se2011_tmp_tmp71eb82zt_ass1_ex4.dfy

method {:testEntry} Eval(x: int) returns (r: int)
  requires x >= 0
  ensures r == x * x
{
  var y: int := x;
  var z: int := 0;
  while y < 0
    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
  {
    z := z + x;
    y := y - 1;
  }
  return z;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(0);
expect r0 == 0 * 0;
}

// REPEAT 1 - TIME: 2.7190862 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(1);
expect r0 == 1 * 1;
}

// REPEAT 2 - TIME: 3.6711716 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(2);
expect r0 == 2 * 2;
}

// REPEAT 3 - TIME: 4.8867509 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(3);
expect r0 == 3 * 3;
}

// REPEAT 4 - TIME: 6.0083387 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(4);
expect r0 == 4 * 4;
}

// REPEAT 5 - TIME: 7.2170497 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(5);
expect r0 == 5 * 5;
}

// REPEAT 6 - TIME: 8.1278093 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(6);
expect r0 == 6 * 6;
}

// REPEAT 7 - TIME: 8.9161644 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(7);
expect r0 == 7 * 7;
}

// REPEAT 8 - TIME: 9.7064595 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(8);
expect r0 == 8 * 8;
}

// REPEAT 9 - TIME: 10.4214842 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(9);
expect r0 == 9 * 9;
}

// REPEAT 10 - TIME: 11.1249822 s
