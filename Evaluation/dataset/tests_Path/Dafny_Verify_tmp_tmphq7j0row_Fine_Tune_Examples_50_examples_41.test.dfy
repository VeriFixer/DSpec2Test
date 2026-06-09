method {:testEntry} main(n: int, k: int) returns (i :int, j: int)
    requires n >= 0
    requires k == 1 || k >= 0
    ensures k + i + j >= 2 * n
{
    i := 0;
    j := 0;
    while(i < n)
        invariant 0 <= i <= n
        invariant j == i * (i + 1) / 2
    {
        i := i + 1;
        j := j + i;
    }
}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1 == 1 || 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(0, 1);
expect 1 + r0 + r1 >= 2 * 0;
}

// REPEAT 1 - TIME: 6.1591937 s

method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(2, 2);
expect 2 + r0 + r1 >= 2 * 2;
}

// REPEAT 2 - TIME: 10.3390614 s

method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 == 1 || 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(3, 3);
expect 3 + r0 + r1 >= 2 * 3;
}

// REPEAT 3 - TIME: 13.8369434 s

method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 == 1 || 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(4, 4);
expect 4 + r0 + r1 >= 2 * 4;
}

// REPEAT 4 - TIME: 17.201179 s

method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 == 1 || 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(5, 5);
expect 5 + r0 + r1 >= 2 * 5;
}

// REPEAT 5 - TIME: 20.382413 s

method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 == 1 || 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(6, 6);
expect 6 + r0 + r1 >= 2 * 6;
}

// REPEAT 6 - TIME: 24.0422667 s

method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 == 1 || 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7, 7);
expect 7 + r0 + r1 >= 2 * 7;
}

// REPEAT 7 - TIME: 27.3574361 s

method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 == 1 || 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(8, 8);
expect 8 + r0 + r1 >= 2 * 8;
}

// REPEAT 8 - TIME: 30.9882877 s

method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 == 1 || 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(9, 9);
expect 9 + r0 + r1 >= 2 * 9;
}

// REPEAT 9 - TIME: 34.7215455 s

method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 == 1 || 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(10, 10);
expect 10 + r0 + r1 >= 2 * 10;
}

// REPEAT 10 - TIME: 38.0710963 s
