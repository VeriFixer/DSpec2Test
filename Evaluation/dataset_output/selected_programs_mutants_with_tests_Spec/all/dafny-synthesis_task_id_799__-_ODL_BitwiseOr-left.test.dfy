// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := n >> (32 - d);
}


method {:test} Test0() {
expect 0 <= 16 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((0 as bv32), 16);
expect r0 == ((0 as bv32) << 16 as bv6) | ((0 as bv32) >> (32 - 16) as bv6);
}

// REPEAT 1 - TIME: 3.0036665 s

method {:test} Test1() {
expect 0 <= 0 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2147483648 as bv32), 0);
expect r0 == ((2147483648 as bv32) << 0 as bv6) | ((2147483648 as bv32) >> (32 - 0) as bv6);
}

// REPEAT 2 - TIME: 4.1145796 s

method {:test} Test2() {
expect 0 <= 1 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 1);
expect r0 == ((1073741824 as bv32) << 1 as bv6) | ((1073741824 as bv32) >> (32 - 1) as bv6);
}

// REPEAT 3 - TIME: 5.0713028 s

method {:test} Test3() {
expect 0 <= 31 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 31);
expect r0 == ((3221225472 as bv32) << 31 as bv6) | ((3221225472 as bv32) >> (32 - 31) as bv6);
}

// REPEAT 4 - TIME: 6.0579198 s

method {:test} Test4() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((536870912 as bv32), 2);
expect r0 == ((536870912 as bv32) << 2 as bv6) | ((536870912 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 5 - TIME: 7.0365734 s

method {:test} Test5() {
expect 0 <= 30 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 30);
expect r0 == ((2684354560 as bv32) << 30 as bv6) | ((2684354560 as bv32) >> (32 - 30) as bv6);
}

// REPEAT 6 - TIME: 7.998234 s

method {:test} Test6() {
expect 0 <= 29 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 29);
expect r0 == ((1610612736 as bv32) << 29 as bv6) | ((1610612736 as bv32) >> (32 - 29) as bv6);
}

// REPEAT 7 - TIME: 8.9693762 s

method {:test} Test7() {
expect 0 <= 28 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 28);
expect r0 == ((3758096384 as bv32) << 28 as bv6) | ((3758096384 as bv32) >> (32 - 28) as bv6);
}

// REPEAT 8 - TIME: 9.6970356 s

method {:test} Test8() {
expect 0 <= 27 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((268435456 as bv32), 27);
expect r0 == ((268435456 as bv32) << 27 as bv6) | ((268435456 as bv32) >> (32 - 27) as bv6);
}

// REPEAT 9 - TIME: 10.5398635 s

method {:test} Test9() {
expect 0 <= 26 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2415919104 as bv32), 26);
expect r0 == ((2415919104 as bv32) << 26 as bv6) | ((2415919104 as bv32) >> (32 - 26) as bv6);
}

// REPEAT 10 - TIME: 11.3154837 s
