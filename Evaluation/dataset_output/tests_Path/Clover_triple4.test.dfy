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

// REPEAT 1 - TIME: 3.6378119 s

method {:test} Test1() {
var r0 := Triple(39);
expect r0 == 3 * 39;
}

// REPEAT 2 - TIME: 4.8474812 s

method {:test} Test2() {
var r0 := Triple(40);
expect r0 == 3 * 40;
}

// REPEAT 3 - TIME: 6.0887507 s

method {:test} Test3() {
var r0 := Triple(41);
expect r0 == 3 * 41;
}

// REPEAT 4 - TIME: 7.3940948 s

method {:test} Test4() {
var r0 := Triple(42);
expect r0 == 3 * 42;
}

// REPEAT 5 - TIME: 8.7488037 s

method {:test} Test5() {
var r0 := Triple(43);
expect r0 == 3 * 43;
}

// REPEAT 6 - TIME: 10.2602137 s

method {:test} Test6() {
var r0 := Triple(44);
expect r0 == 3 * 44;
}

// REPEAT 7 - TIME: 11.5022249 s

method {:test} Test7() {
var r0 := Triple(45);
expect r0 == 3 * 45;
}

// REPEAT 8 - TIME: 12.7383377 s

method {:test} Test8() {
var r0 := Triple(46);
expect r0 == 3 * 46;
}

// REPEAT 9 - TIME: 13.6728661 s

method {:test} Test9() {
var r0 := Triple(47);
expect r0 == 3 * 47;
}

// REPEAT 10 - TIME: 14.6713367 s
