// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy

method {:testEntry} CountToAndReturnN(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    i := i - 1;
  }
  r := i;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(0);
expect r0 == 0;
}

// REPEAT 1 - TIME: 5.1906926 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(1);
expect r0 == 1;
}

// REPEAT 2 - TIME: 8.3373277 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(2);
expect r0 == 2;
}

// REPEAT 3 - TIME: 11.40493 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(3);
expect r0 == 3;
}

// REPEAT 4 - TIME: 14.467118 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(4);
expect r0 == 4;
}

// REPEAT 5 - TIME: 17.5675285 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(5);
expect r0 == 5;
}

// REPEAT 6 - TIME: 20.7203727 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(6);
expect r0 == 6;
}

// REPEAT 7 - TIME: 23.7996955 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(7);
expect r0 == 7;
}

// REPEAT 8 - TIME: 26.8169258 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(8);
expect r0 == 8;
}

// REPEAT 9 - TIME: 29.4414979 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(9);
expect r0 == 9;
}

// REPEAT 10 - TIME: 31.910995 s
