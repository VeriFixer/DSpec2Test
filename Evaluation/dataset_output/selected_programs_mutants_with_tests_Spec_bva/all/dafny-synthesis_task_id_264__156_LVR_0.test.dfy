// dafny-synthesis_task_id_264.dfy

method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
  requires humanYears >= 0
  ensures dogYears == 7 * humanYears
{
  dogYears := 0 * humanYears;
}


method {:test} Test0() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(38);
expect r0 == 7 * 38;
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(0);
expect r0 == 7 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(100);
expect r0 == 7 * 100;
}

// REPEAT 1 - TIME: 5.2695764 s

method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(101);
expect r0 == 7 * 101;
}

// REPEAT 2 - TIME: 6.2077379 s

method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(102);
expect r0 == 7 * 102;
}

// REPEAT 3 - TIME: 7.0982497 s

method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(103);
expect r0 == 7 * 103;
}

// REPEAT 4 - TIME: 7.8767718 s

method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(104);
expect r0 == 7 * 104;
}

// REPEAT 5 - TIME: 8.5448249 s

method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(105);
expect r0 == 7 * 105;
}

// REPEAT 6 - TIME: 9.1905505 s

method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(106);
expect r0 == 7 * 106;
}

// REPEAT 7 - TIME: 9.846895 s

method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(107);
expect r0 == 7 * 107;
}

// REPEAT 8 - TIME: 10.4710934 s

method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(108);
expect r0 == 7 * 108;
}

// REPEAT 9 - TIME: 10.992336 s

method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(109);
expect r0 == 7 * 109;
}

// REPEAT 10 - TIME: 11.5395662 s
