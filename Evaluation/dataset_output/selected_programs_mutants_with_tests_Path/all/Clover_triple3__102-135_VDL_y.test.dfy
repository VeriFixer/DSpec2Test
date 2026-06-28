// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x == 0 {
    r := 0;
  } else {
    r := x;
  }
}


method {:test} Test0() {
var r0 := Triple(0);
expect r0 == 3 * 0;
}
method {:test} Test1() {
var r0 := Triple(1);
expect r0 == 3 * 1;
}

// REPEAT 1 - TIME: 4.7443865 s

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 2 - TIME: 7.0145361 s

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 3 - TIME: 9.1142788 s

method {:test} Test4() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 4 - TIME: 11.0463354 s

method {:test} Test5() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 5 - TIME: 12.8174671 s

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 6 - TIME: 14.6840534 s

method {:test} Test7() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 7 - TIME: 16.368634 s

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 8 - TIME: 17.9526344 s

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 9 - TIME: 19.5631357 s

method {:test} Test10() {
var r0 := Triple(48);
expect r0 == 3 * 48;
}

// REPEAT 10 - TIME: 21.0310196 s
