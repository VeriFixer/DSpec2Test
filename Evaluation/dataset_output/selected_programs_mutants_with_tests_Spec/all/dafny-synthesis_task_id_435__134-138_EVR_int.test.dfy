// dafny-synthesis_task_id_435.dfy

method {:testEntry} LastDigit(n: int) returns (d: int)
  requires n >= 0
  ensures 0 <= d < 10
  ensures n % 10 == d
{
  d := 0;
}


method {:test} Test0() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(8);
expect 0 <= r0 < 10;
expect 8 % 10 == r0;
}

// REPEAT 1 - TIME: 3.0295958 s

method {:test} Test1() {
expect 12370 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12370);
expect 0 <= r0 < 10;
expect 12370 % 10 == r0;
}

// REPEAT 2 - TIME: 4.2564154 s

method {:test} Test2() {
expect 12380 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12380);
expect 0 <= r0 < 10;
expect 12380 % 10 == r0;
}

// REPEAT 3 - TIME: 5.2943992 s

method {:test} Test3() {
expect 12390 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12390);
expect 0 <= r0 < 10;
expect 12390 % 10 == r0;
}

// REPEAT 4 - TIME: 6.388086 s

method {:test} Test4() {
expect 12400 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12400);
expect 0 <= r0 < 10;
expect 12400 % 10 == r0;
}

// REPEAT 5 - TIME: 7.3740739 s

method {:test} Test5() {
expect 12410 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12410);
expect 0 <= r0 < 10;
expect 12410 % 10 == r0;
}

// REPEAT 6 - TIME: 8.0913257 s

method {:test} Test6() {
expect 12420 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12420);
expect 0 <= r0 < 10;
expect 12420 % 10 == r0;
}

// REPEAT 7 - TIME: 8.7680286 s

method {:test} Test7() {
expect 12430 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12430);
expect 0 <= r0 < 10;
expect 12430 % 10 == r0;
}

// REPEAT 8 - TIME: 9.4036587 s

method {:test} Test8() {
expect 12440 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12440);
expect 0 <= r0 < 10;
expect 12440 % 10 == r0;
}

// REPEAT 9 - TIME: 10.1004624 s

method {:test} Test9() {
expect 12450 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LastDigit(12450);
expect 0 <= r0 < 10;
expect 12450 % 10 == r0;
}

// REPEAT 10 - TIME: 10.6394221 s
