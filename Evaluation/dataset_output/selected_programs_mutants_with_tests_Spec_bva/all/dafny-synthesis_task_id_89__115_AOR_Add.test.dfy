// dafny-synthesis_task_id_89.dfy

method {:testEntry} ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
{
  m := n + 1;
}


method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(1);
expect r0 + 1 == 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(100);
expect r0 + 1 == 100;
}
method {:test} Test4() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(101);
expect r0 + 1 == 101;
}

// REPEAT 1 - TIME: 7.6222413 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(102);
expect r0 + 1 == 102;
}

// REPEAT 2 - TIME: 8.7253886 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(103);
expect r0 + 1 == 103;
}

// REPEAT 3 - TIME: 9.6544307 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(104);
expect r0 + 1 == 104;
}

// REPEAT 4 - TIME: 10.5977139 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(105);
expect r0 + 1 == 105;
}

// REPEAT 5 - TIME: 11.5274757 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(106);
expect r0 + 1 == 106;
}

// REPEAT 6 - TIME: 12.5353711 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(107);
expect r0 + 1 == 107;
}

// REPEAT 7 - TIME: 13.4582859 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(108);
expect r0 + 1 == 108;
}

// REPEAT 8 - TIME: 14.2531677 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(109);
expect r0 + 1 == 109;
}

// REPEAT 9 - TIME: 15.0873668 s

method {:test} Test15() {
expect 110 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(110);
expect r0 + 1 == 110;
}

// REPEAT 10 - TIME: 15.8856512 s
