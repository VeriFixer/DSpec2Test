// M2_tmp_tmp2laaavvl_Software Verification_Exercices_Exo4-CountAndReturn.dfy

method {:testEntry} CountToAndReturnN(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
  }
  r := i;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(0);
expect r0 == 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(100);
expect r0 == 100;
}

// REPEAT 1 - TIME: 5.7703825 s

method {:test} Test7() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(101);
expect r0 == 101;
}

// REPEAT 2 - TIME: 6.7220435 s

method {:test} Test8() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(102);
expect r0 == 102;
}

// REPEAT 3 - TIME: 7.516902 s

method {:test} Test9() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(103);
expect r0 == 103;
}

// REPEAT 4 - TIME: 8.223543 s

method {:test} Test10() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(104);
expect r0 == 104;
}

// REPEAT 5 - TIME: 8.9632621 s

method {:test} Test11() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(105);
expect r0 == 105;
}

// REPEAT 6 - TIME: 9.5758528 s

method {:test} Test12() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(106);
expect r0 == 106;
}

// REPEAT 7 - TIME: 10.2452803 s

method {:test} Test13() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(107);
expect r0 == 107;
}

// REPEAT 8 - TIME: 10.9035422 s

method {:test} Test14() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(108);
expect r0 == 108;
}

// REPEAT 9 - TIME: 11.5126832 s

method {:test} Test15() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CountToAndReturnN(109);
expect r0 == 109;
}

// REPEAT 10 - TIME: 12.159913 s
