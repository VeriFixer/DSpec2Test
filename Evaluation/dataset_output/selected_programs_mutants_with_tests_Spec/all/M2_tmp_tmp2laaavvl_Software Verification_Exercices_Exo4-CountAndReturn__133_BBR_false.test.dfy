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

// REPEAT 1 - TIME: 2.596488 s

method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(1);
expect r0 == 1;
}

// REPEAT 2 - TIME: 3.4070184 s

method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(2);
expect r0 == 2;
}

// REPEAT 3 - TIME: 4.3672581 s

method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(3);
expect r0 == 3;
}

// REPEAT 4 - TIME: 5.1710727 s

method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(4);
expect r0 == 4;
}

// REPEAT 5 - TIME: 6.0104699 s

method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(5);
expect r0 == 5;
}

// REPEAT 6 - TIME: 6.9776228 s

method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(6);
expect r0 == 6;
}

// REPEAT 7 - TIME: 7.8059861 s

method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(7);
expect r0 == 7;
}

// REPEAT 8 - TIME: 8.5356907 s

method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(8);
expect r0 == 8;
}

// REPEAT 9 - TIME: 9.2337227 s

method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(9);
expect r0 == 9;
}

// REPEAT 10 - TIME: 9.955929 s
