// dafny-synthesis_task_id_264.dfy

method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
  requires humanYears >= 0
  ensures dogYears == 7 * humanYears
{
  dogYears := 7 + humanYears;
}


method {:test} Test0() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(38);
expect r0 == 7 * 38;
}

// REPEAT 1 - TIME: 3.6614954 s

method {:test} Test1() {
expect 39 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(39);
expect r0 == 7 * 39;
}

// REPEAT 2 - TIME: 5.0575659 s

method {:test} Test2() {
expect 40 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(40);
expect r0 == 7 * 40;
}

// REPEAT 3 - TIME: 6.4290187 s

method {:test} Test3() {
expect 41 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(41);
expect r0 == 7 * 41;
}

// REPEAT 4 - TIME: 7.7561809 s

method {:test} Test4() {
expect 42 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(42);
expect r0 == 7 * 42;
}

// REPEAT 5 - TIME: 8.8645382 s

method {:test} Test5() {
expect 43 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(43);
expect r0 == 7 * 43;
}

// REPEAT 6 - TIME: 9.937837 s

method {:test} Test6() {
expect 44 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(44);
expect r0 == 7 * 44;
}

// REPEAT 7 - TIME: 10.9359049 s

method {:test} Test7() {
expect 45 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(45);
expect r0 == 7 * 45;
}

// REPEAT 8 - TIME: 11.8657919 s

method {:test} Test8() {
expect 46 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(46);
expect r0 == 7 * 46;
}

// REPEAT 9 - TIME: 12.8101463 s

method {:test} Test9() {
expect 47 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(47);
expect r0 == 7 * 47;
}

// REPEAT 10 - TIME: 13.8592145 s
