// se2011_tmp_tmp71eb82zt_ass1_ex4.dfy

method {:testEntry} Eval(x: int) returns (r: int)
  requires x >= 0
  ensures r == x * x
{
  var y: int := x;
  var z: int := 0;
  while y > 0
    invariant 0 <= y <= x && z == x * (x - y)
    decreases y
  {
    z := z * x;
    y := y - 1;
  }
  return z;
}


method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(0);
expect r0 == 0 * 0;
}
method {:test} Test2() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 7.8810965 s

method {:test} Test7() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 8.9569711 s

method {:test} Test8() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 10.1119992 s

method {:test} Test9() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 10.9850204 s

method {:test} Test10() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 11.8948567 s

method {:test} Test11() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(105);
expect r0 == 105 * 105;
}

// REPEAT 6 - TIME: 12.7567745 s

method {:test} Test12() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 13.5991188 s

method {:test} Test13() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(107);
expect r0 == 107 * 107;
}

// REPEAT 8 - TIME: 14.5961194 s

method {:test} Test14() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 15.5838875 s

method {:test} Test15() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Eval(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 16.5828174 s
