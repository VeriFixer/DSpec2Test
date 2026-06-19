// dafny-synthesis_task_id_799.dfy

method {:testEntry} RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  requires 0 <= d < 32
  ensures result == (n << d) | (n >> (32 - d))
{
  result := (n << d) | (n >> 32 * d);
}


method {:test} Test0() {
expect 0 <= 0 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((0 as bv32), 0);
expect r0 == ((0 as bv32) << 0 as bv6) | ((0 as bv32) >> (32 - 0) as bv6);
}

// REPEAT 1 - TIME: 2.2684125 s

method {:test} Test1() {
expect 0 <= 1 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2147483648 as bv32), 1);
expect r0 == ((2147483648 as bv32) << 1 as bv6) | ((2147483648 as bv32) >> (32 - 1) as bv6);
}

// REPEAT 2 - TIME: 3.0824518 s

method {:test} Test2() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 2);
expect r0 == ((1073741824 as bv32) << 2 as bv6) | ((1073741824 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 3 - TIME: 3.7927394 s

method {:test} Test3() {
expect 0 <= 3 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 3);
expect r0 == ((3221225472 as bv32) << 3 as bv6) | ((3221225472 as bv32) >> (32 - 3) as bv6);
}

// REPEAT 4 - TIME: 4.4874641 s

method {:test} Test4() {
expect 0 <= 4 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((536870912 as bv32), 4);
expect r0 == ((536870912 as bv32) << 4 as bv6) | ((536870912 as bv32) >> (32 - 4) as bv6);
}

// REPEAT 5 - TIME: 5.2832904 s

method {:test} Test5() {
expect 0 <= 6 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 6);
expect r0 == ((2684354560 as bv32) << 6 as bv6) | ((2684354560 as bv32) >> (32 - 6) as bv6);
}

// REPEAT 6 - TIME: 6.0336982 s

method {:test} Test6() {
expect 0 <= 5 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 5);
expect r0 == ((1610612736 as bv32) << 5 as bv6) | ((1610612736 as bv32) >> (32 - 5) as bv6);
}

// REPEAT 7 - TIME: 6.6924052 s

method {:test} Test7() {
expect 0 <= 7 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 7);
expect r0 == ((3758096384 as bv32) << 7 as bv6) | ((3758096384 as bv32) >> (32 - 7) as bv6);
}

// REPEAT 8 - TIME: 7.406633 s

method {:test} Test8() {
expect 0 <= 8 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((268435456 as bv32), 8);
expect r0 == ((268435456 as bv32) << 8 as bv6) | ((268435456 as bv32) >> (32 - 8) as bv6);
}

// REPEAT 9 - TIME: 8.1334779 s

method {:test} Test9() {
expect 0 <= 12 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2415919104 as bv32), 12);
expect r0 == ((2415919104 as bv32) << 12 as bv6) | ((2415919104 as bv32) >> (32 - 12) as bv6);
}

// REPEAT 10 - TIME: 8.7290118 s
