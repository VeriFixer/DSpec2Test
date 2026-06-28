// Dafny_Verify_tmp_tmphq7j0row_Generated_Code_rand.dfy

method {:testEntry} Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x - y;
  while x > 0
    invariant x >= 0
    invariant z == x * y
    decreases x
  {
    x := x - 1;
    z := z - y;
  }
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(0, 0);
expect r0 == 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(100, 0);
expect r0 == 0;
}
method {:test} Test4() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(0, 100);
expect r0 == 0;
}

// REPEAT 1 - TIME: 7.995105 s

method {:test} Test8() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(101, 101);
expect r0 == 0;
}

// REPEAT 2 - TIME: 9.1654978 s

method {:test} Test9() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(102, 102);
expect r0 == 0;
}

// REPEAT 3 - TIME: 10.2075313 s

method {:test} Test10() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(103, 103);
expect r0 == 0;
}

// REPEAT 4 - TIME: 11.2268646 s

method {:test} Test11() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(104, 104);
expect r0 == 0;
}

// REPEAT 5 - TIME: 12.3041614 s

method {:test} Test12() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(105, 105);
expect r0 == 0;
}

// REPEAT 6 - TIME: 13.3476879 s

method {:test} Test13() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(106, 106);
expect r0 == 0;
}

// REPEAT 7 - TIME: 14.3736957 s

method {:test} Test14() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(107, 107);
expect r0 == 0;
}

// REPEAT 8 - TIME: 15.1667333 s

method {:test} Test15() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(108, 108);
expect r0 == 0;
}

// REPEAT 9 - TIME: 15.9429212 s

method {:test} Test16() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Main(109, 109);
expect r0 == 0;
}

// REPEAT 10 - TIME: 16.7433466 s
