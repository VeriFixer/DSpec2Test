// dafny-synthesis_task_id_89.dfy

method {:testEntry} ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
{
  m := -(n - 1);
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(1);
expect r0 + 1 == 1;
}

// REPEAT 1 - TIME: 2.1726787 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(2);
expect r0 + 1 == 2;
}

// REPEAT 2 - TIME: 3.2588144 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(3);
expect r0 + 1 == 3;
}

// REPEAT 3 - TIME: 4.0622457 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(4);
expect r0 + 1 == 4;
}

// REPEAT 4 - TIME: 4.8069382 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(5);
expect r0 + 1 == 5;
}

// REPEAT 5 - TIME: 5.5382766 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(6);
expect r0 + 1 == 6;
}

// REPEAT 6 - TIME: 6.3328507 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(7);
expect r0 + 1 == 7;
}

// REPEAT 7 - TIME: 6.9521163 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(8);
expect r0 + 1 == 8;
}

// REPEAT 8 - TIME: 7.5488199 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(9);
expect r0 + 1 == 9;
}

// REPEAT 9 - TIME: 8.1665986 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(10);
expect r0 + 1 == 10;
}

// REPEAT 10 - TIME: 8.7537739 s
