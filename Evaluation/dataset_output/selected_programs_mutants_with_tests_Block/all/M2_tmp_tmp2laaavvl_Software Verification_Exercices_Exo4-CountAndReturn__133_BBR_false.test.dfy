// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy

method {:testEntry} CountToAndReturnN(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
{
  var i := 0;
  while false
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  r := i;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(0);
expect r0 == 0;
}

// REPEAT 1 - TIME: 2.158332 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(1);
expect r0 == 1;
}

// REPEAT 2 - TIME: 3.2349429 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(2);
expect r0 == 2;
}

// REPEAT 3 - TIME: 4.2368518 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(3);
expect r0 == 3;
}

// REPEAT 4 - TIME: 5.1766235 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(4);
expect r0 == 4;
}

// REPEAT 5 - TIME: 6.0657411 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(5);
expect r0 == 5;
}

// REPEAT 6 - TIME: 6.9179619 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(6);
expect r0 == 6;
}

// REPEAT 7 - TIME: 7.8832594 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(7);
expect r0 == 7;
}

// REPEAT 8 - TIME: 8.7313469 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(8);
expect r0 == 8;
}

// REPEAT 9 - TIME: 9.4499883 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(9);
expect r0 == 9;
}

// REPEAT 10 - TIME: 10.1522133 s
