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
method {:test} Test3() {
expect 0 <= 0 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((0 as bv32), 0);
expect r0 == ((0 as bv32) << 0 as bv6) | ((0 as bv32) >> (32 - 0) as bv6);
}
method {:test} Test4() {
expect 0 <= 31 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((0 as bv32), 31);
expect r0 == ((0 as bv32) << 31 as bv6) | ((0 as bv32) >> (32 - 31) as bv6);
}

// REPEAT 1 - TIME: 9.0306257 s

method {:test} Test10() {
expect 0 <= 30 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2147483648 as bv32), 30);
expect r0 == ((2147483648 as bv32) << 30 as bv6) | ((2147483648 as bv32) >> (32 - 30) as bv6);
}

// REPEAT 2 - TIME: 10.1387329 s

method {:test} Test11() {
expect 0 <= 1 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1073741824 as bv32), 1);
expect r0 == ((1073741824 as bv32) << 1 as bv6) | ((1073741824 as bv32) >> (32 - 1) as bv6);
}

// REPEAT 3 - TIME: 11.2057606 s

method {:test} Test12() {
expect 0 <= 29 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3221225472 as bv32), 29);
expect r0 == ((3221225472 as bv32) << 29 as bv6) | ((3221225472 as bv32) >> (32 - 29) as bv6);
}

// REPEAT 4 - TIME: 12.2918717 s

method {:test} Test13() {
expect 0 <= 2 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((536870912 as bv32), 2);
expect r0 == ((536870912 as bv32) << 2 as bv6) | ((536870912 as bv32) >> (32 - 2) as bv6);
}

// REPEAT 5 - TIME: 13.1421182 s

method {:test} Test14() {
expect 0 <= 28 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2684354560 as bv32), 28);
expect r0 == ((2684354560 as bv32) << 28 as bv6) | ((2684354560 as bv32) >> (32 - 28) as bv6);
}

// REPEAT 6 - TIME: 14.2622315 s

method {:test} Test15() {
expect 0 <= 27 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((1610612736 as bv32), 27);
expect r0 == ((1610612736 as bv32) << 27 as bv6) | ((1610612736 as bv32) >> (32 - 27) as bv6);
}

// REPEAT 7 - TIME: 15.4054817 s

method {:test} Test16() {
expect 0 <= 26 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((3758096384 as bv32), 26);
expect r0 == ((3758096384 as bv32) << 26 as bv6) | ((3758096384 as bv32) >> (32 - 26) as bv6);
}

// REPEAT 8 - TIME: 16.6476087 s

method {:test} Test17() {
expect 0 <= 3 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((268435456 as bv32), 3);
expect r0 == ((268435456 as bv32) << 3 as bv6) | ((268435456 as bv32) >> (32 - 3) as bv6);
}

// REPEAT 9 - TIME: 17.6963831 s

method {:test} Test18() {
expect 0 <= 25 < 32, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RotateLeftBits((2415919104 as bv32), 25);
expect r0 == ((2415919104 as bv32) << 25 as bv6) | ((2415919104 as bv32) >> (32 - 25) as bv6);
}

// REPEAT 10 - TIME: 18.5726285 s
