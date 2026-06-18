// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 - a;
}


method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 * a;
}

method {:test} Test0() {
var r0, r1 := DoubleQuadruple(0);
expect r0 == 2 * 0 && r1 == 4 * 0;
}

// REPEAT 1 - TIME: 2.3972982 s

method {:test} Test1() {
var r0, r1 := DoubleQuadruple(1);
expect r0 == 2 * 1 && r1 == 4 * 1;
}

// REPEAT 2 - TIME: 3.2870632 s

method {:test} Test2() {
var r0, r1 := DoubleQuadruple(40);
expect r0 == 2 * 40 && r1 == 4 * 40;
}

// REPEAT 3 - TIME: 4.1690875 s

method {:test} Test3() {
var r0, r1 := DoubleQuadruple(41);
expect r0 == 2 * 41 && r1 == 4 * 41;
}

// REPEAT 4 - TIME: 4.9046674 s

method {:test} Test4() {
var r0, r1 := DoubleQuadruple(42);
expect r0 == 2 * 42 && r1 == 4 * 42;
}

// REPEAT 5 - TIME: 5.6046555 s

method {:test} Test5() {
var r0, r1 := DoubleQuadruple(43);
expect r0 == 2 * 43 && r1 == 4 * 43;
}

// REPEAT 6 - TIME: 6.2487319 s

method {:test} Test6() {
var r0, r1 := DoubleQuadruple(44);
expect r0 == 2 * 44 && r1 == 4 * 44;
}

// REPEAT 7 - TIME: 6.6885121 s

method {:test} Test7() {
var r0, r1 := DoubleQuadruple(45);
expect r0 == 2 * 45 && r1 == 4 * 45;
}

// REPEAT 8 - TIME: 7.1457117 s

method {:test} Test8() {
var r0, r1 := DoubleQuadruple(46);
expect r0 == 2 * 46 && r1 == 4 * 46;
}

// REPEAT 9 - TIME: 7.5487657 s

method {:test} Test9() {
var r0, r1 := DoubleQuadruple(47);
expect r0 == 2 * 47 && r1 == 4 * 47;
}

// REPEAT 10 - TIME: 7.9750663 s
