method {:testEntry} CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
{
    area := 6 * size * size;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(1);
expect r0 == 6 * 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(100);
expect r0 == 6 * 100 * 100;
}

// REPEAT 1 - TIME: 4.5282323 s

method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(101);
expect r0 == 6 * 101 * 101;
}

// REPEAT 2 - TIME: 5.2843361 s

method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(102);
expect r0 == 6 * 102 * 102;
}

// REPEAT 3 - TIME: 6.0879363 s

method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(103);
expect r0 == 6 * 103 * 103;
}

// REPEAT 4 - TIME: 6.7821607 s

method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(104);
expect r0 == 6 * 104 * 104;
}

// REPEAT 5 - TIME: 7.4067628 s

method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(105);
expect r0 == 6 * 105 * 105;
}

// REPEAT 6 - TIME: 7.9842698 s

method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(106);
expect r0 == 6 * 106 * 106;
}

// REPEAT 7 - TIME: 8.6408338 s

method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(107);
expect r0 == 6 * 107 * 107;
}

// REPEAT 8 - TIME: 9.341948 s

method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(108);
expect r0 == 6 * 108 * 108;
}

// REPEAT 9 - TIME: 9.8980662 s

method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(109);
expect r0 == 6 * 109 * 109;
}

// REPEAT 10 - TIME: 10.5132325 s
