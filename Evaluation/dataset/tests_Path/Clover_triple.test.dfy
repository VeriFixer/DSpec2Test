method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r:= x*3;
}

method {:test} Test0() {
var r0 := Triple(38);
expect r0 == 3 * 38;
}

// REPEAT 1 - TIME: 1.837281 s

method {:test} Test1() {
var r0 := Triple(39);
expect r0 == 3 * 39;
}

// REPEAT 2 - TIME: 2.4114017 s

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 3 - TIME: 2.963189 s

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 4 - TIME: 3.548949 s

method {:test} Test4() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 5 - TIME: 4.1738045 s

method {:test} Test5() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 6 - TIME: 4.8161107 s

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 7 - TIME: 5.4421325 s

method {:test} Test7() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 8 - TIME: 6.0434274 s

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 9 - TIME: 6.624513 s

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 10 - TIME: 7.2260687 s
