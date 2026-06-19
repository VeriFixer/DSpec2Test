// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := x;
  b := a;
}


method {:test} Test0() {
var r0, r1 := DoubleQuadruple(0);
expect r0 == 2 * 0 && r1 == 4 * 0;
}
method {:test} Test1() {
var r0, r1 := DoubleQuadruple(-100);
expect r0 == 2 * -100 && r1 == 4 * -100;
}
method {:test} Test2() {
var r0, r1 := DoubleQuadruple(100);
expect r0 == 2 * 100 && r1 == 4 * 100;
}

// REPEAT 1 - TIME: 5.5763238 s

method {:test} Test7() {
var r0, r1 := DoubleQuadruple(101);
expect r0 == 2 * 101 && r1 == 4 * 101;
}

// REPEAT 2 - TIME: 6.5109127 s

method {:test} Test8() {
var r0, r1 := DoubleQuadruple(102);
expect r0 == 2 * 102 && r1 == 4 * 102;
}

// REPEAT 3 - TIME: 7.3196202 s

method {:test} Test9() {
var r0, r1 := DoubleQuadruple(103);
expect r0 == 2 * 103 && r1 == 4 * 103;
}

// REPEAT 4 - TIME: 8.1312254 s

method {:test} Test10() {
var r0, r1 := DoubleQuadruple(104);
expect r0 == 2 * 104 && r1 == 4 * 104;
}

// REPEAT 5 - TIME: 8.7978765 s

method {:test} Test11() {
var r0, r1 := DoubleQuadruple(105);
expect r0 == 2 * 105 && r1 == 4 * 105;
}

// REPEAT 6 - TIME: 9.4174172 s

method {:test} Test12() {
var r0, r1 := DoubleQuadruple(106);
expect r0 == 2 * 106 && r1 == 4 * 106;
}

// REPEAT 7 - TIME: 10.1275099 s

method {:test} Test13() {
var r0, r1 := DoubleQuadruple(107);
expect r0 == 2 * 107 && r1 == 4 * 107;
}

// REPEAT 8 - TIME: 10.7685155 s

method {:test} Test14() {
var r0, r1 := DoubleQuadruple(108);
expect r0 == 2 * 108 && r1 == 4 * 108;
}

// REPEAT 9 - TIME: 11.3947719 s

method {:test} Test15() {
var r0, r1 := DoubleQuadruple(109);
expect r0 == 2 * 109 && r1 == 4 * 109;
}

// REPEAT 10 - TIME: 11.8348578 s
