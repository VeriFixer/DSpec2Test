method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test0() {
var r0 := Triple(38);
expect r0 == 3 * 38;
}

// REPEAT 1 - TIME: 2.4851284 s

method {:test} Test1() {
var r0 := Triple(39);
expect r0 == 3 * 39;
}

// REPEAT 2 - TIME: 3.6329494 s

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 3 - TIME: 4.9392897 s

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 4 - TIME: 6.1370231 s

method {:test} Test4() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 5 - TIME: 7.4902823 s

method {:test} Test5() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 6 - TIME: 8.6307618 s

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 7 - TIME: 9.8124265 s

method {:test} Test7() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 8 - TIME: 10.8074082 s

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 9 - TIME: 11.8457545 s

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 10 - TIME: 12.8736076 s
