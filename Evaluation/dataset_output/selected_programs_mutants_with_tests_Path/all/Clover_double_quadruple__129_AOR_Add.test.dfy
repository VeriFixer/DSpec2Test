// Clover_double_quadruple.dfy

method {:testEntry} DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  b := 2 + a;
}


method {:test} Test0() {
var r0, r1 := DoubleQuadruple(1236);
expect r0 == 2 * 1236 && r1 == 4 * 1236;
}

// REPEAT 1 - TIME: 2.8555668 s

method {:test} Test1() {
var r0, r1 := DoubleQuadruple(1237);
expect r0 == 2 * 1237 && r1 == 4 * 1237;
}

// REPEAT 2 - TIME: 3.814813 s

method {:test} Test2() {
var r0, r1 := DoubleQuadruple(1238);
expect r0 == 2 * 1238 && r1 == 4 * 1238;
}

// REPEAT 3 - TIME: 4.8650988 s

method {:test} Test3() {
var r0, r1 := DoubleQuadruple(1239);
expect r0 == 2 * 1239 && r1 == 4 * 1239;
}

// REPEAT 4 - TIME: 5.8137656 s

method {:test} Test4() {
var r0, r1 := DoubleQuadruple(1240);
expect r0 == 2 * 1240 && r1 == 4 * 1240;
}

// REPEAT 5 - TIME: 6.729213 s

method {:test} Test5() {
var r0, r1 := DoubleQuadruple(1241);
expect r0 == 2 * 1241 && r1 == 4 * 1241;
}

// REPEAT 6 - TIME: 7.640338 s

method {:test} Test6() {
var r0, r1 := DoubleQuadruple(1242);
expect r0 == 2 * 1242 && r1 == 4 * 1242;
}

// REPEAT 7 - TIME: 8.3842311 s

method {:test} Test7() {
var r0, r1 := DoubleQuadruple(1243);
expect r0 == 2 * 1243 && r1 == 4 * 1243;
}

// REPEAT 8 - TIME: 9.2951127 s

method {:test} Test8() {
var r0, r1 := DoubleQuadruple(1244);
expect r0 == 2 * 1244 && r1 == 4 * 1244;
}

// REPEAT 9 - TIME: 10.047711 s

method {:test} Test9() {
var r0, r1 := DoubleQuadruple(1245);
expect r0 == 2 * 1245 && r1 == 4 * 1245;
}

// REPEAT 10 - TIME: 10.8909022 s
