method {:testEntry} LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
{
    area := 4 * size * size;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(1);
expect r0 == 4 * 1 * 1;
}

// REPEAT 1 - TIME: 2.0666361 s

method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(2);
expect r0 == 4 * 2 * 2;
}

// REPEAT 2 - TIME: 2.7774084 s

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(3);
expect r0 == 4 * 3 * 3;
}

// REPEAT 3 - TIME: 3.4368651 s

method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(4);
expect r0 == 4 * 4 * 4;
}

// REPEAT 4 - TIME: 4.1794818 s

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(5);
expect r0 == 4 * 5 * 5;
}

// REPEAT 5 - TIME: 5.0146136 s

method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(6);
expect r0 == 4 * 6 * 6;
}

// REPEAT 6 - TIME: 5.7695631 s

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(7);
expect r0 == 4 * 7 * 7;
}

// REPEAT 7 - TIME: 6.3746164 s

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(8);
expect r0 == 4 * 8 * 8;
}

// REPEAT 8 - TIME: 6.8808105 s

method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(9);
expect r0 == 4 * 9 * 9;
}

// REPEAT 9 - TIME: 7.3232416 s

method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(10);
expect r0 == 4 * 10 * 10;
}

// REPEAT 10 - TIME: 7.8358746 s
