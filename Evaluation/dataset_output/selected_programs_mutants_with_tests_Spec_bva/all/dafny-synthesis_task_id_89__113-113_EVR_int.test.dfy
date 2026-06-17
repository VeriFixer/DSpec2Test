// dafny-synthesis_task_id_89.dfy

method {:testEntry} ClosestSmaller(n: int) returns (m: int)
  requires n > 0
  ensures m + 1 == n
{
  m := 0 - 1;
}


method {:testEntry} ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
{
    m := n - 1;
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

// REPEAT 1 - TIME: 5.3027572 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(102);
expect r0 + 1 == 102;
}

// REPEAT 2 - TIME: 6.0707402 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(103);
expect r0 + 1 == 103;
}

// REPEAT 3 - TIME: 6.8645739 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(104);
expect r0 + 1 == 104;
}

// REPEAT 4 - TIME: 7.4790316 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(105);
expect r0 + 1 == 105;
}

// REPEAT 5 - TIME: 8.1996448 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(106);
expect r0 + 1 == 106;
}

// REPEAT 6 - TIME: 8.8631962 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(107);
expect r0 + 1 == 107;
}

// REPEAT 7 - TIME: 9.5209941 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(108);
expect r0 + 1 == 108;
}

// REPEAT 8 - TIME: 10.1119969 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(109);
expect r0 + 1 == 109;
}

// REPEAT 9 - TIME: 10.7165547 s

method {:test} Test15() {
expect 110 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(110);
expect r0 + 1 == 110;
}

// REPEAT 10 - TIME: 11.396162 s
