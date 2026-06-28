// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x == 0 {
    r := 0;
  } else {
    var y := 2 - x;
    r := x + y;
  }
}


method {:test} Test0() {
var r0 := Triple(1);
expect r0 == 3 * 1;
}
method {:test} Test1() {
var r0 := Triple(0);
expect r0 == 3 * 0;
}

// REPEAT 1 - TIME: 2.0661515 s

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 2 - TIME: 2.8752906 s

method {:test} Test4() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 3 - TIME: 3.7130082 s

method {:test} Test6() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 4 - TIME: 4.6413497 s

method {:test} Test8() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 5 - TIME: 5.7140832 s

method {:test} Test10() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 6 - TIME: 6.6565905 s

method {:test} Test12() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 7 - TIME: 7.6258253 s

method {:test} Test14() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 8 - TIME: 8.4510538 s

method {:test} Test16() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 9 - TIME: 9.1568347 s

method {:test} Test18() {
var r0 := Triple(48);
expect r0 == 3 * 48;
}

// REPEAT 10 - TIME: 9.6821778 s
