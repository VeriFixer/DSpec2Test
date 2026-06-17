// Clover_triple4.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  var y := x;
  r := y + x;
}


method {:testEntry} Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  r := y+x;
}

method {:test} Test0() {
var r0 := Triple(2573);
expect r0 == 3 * 2573;
}
method {:test} Test1() {
var r0 := Triple(-100);
expect r0 == 3 * -100;
}
method {:test} Test2() {
var r0 := Triple(100);
expect r0 == 3 * 100;
}
method {:test} Test3() {
var r0 := Triple(38);
expect r0 == 3 * 38;
}

// REPEAT 1 - TIME: 4.0738877 s

method {:test} Test6() {
var r0 := Triple(2574);
expect r0 == 3 * 2574;
}

// REPEAT 2 - TIME: 4.6955387 s

method {:test} Test7() {
var r0 := Triple(2575);
expect r0 == 3 * 2575;
}

// REPEAT 3 - TIME: 5.2607429 s

method {:test} Test8() {
var r0 := Triple(2576);
expect r0 == 3 * 2576;
}

// REPEAT 4 - TIME: 5.8375628 s

method {:test} Test9() {
var r0 := Triple(2577);
expect r0 == 3 * 2577;
}

// REPEAT 5 - TIME: 6.3791238 s

method {:test} Test10() {
var r0 := Triple(2578);
expect r0 == 3 * 2578;
}

// REPEAT 6 - TIME: 6.9655765 s

method {:test} Test11() {
var r0 := Triple(2579);
expect r0 == 3 * 2579;
}

// REPEAT 7 - TIME: 7.5290296 s

method {:test} Test12() {
var r0 := Triple(2580);
expect r0 == 3 * 2580;
}

// REPEAT 8 - TIME: 8.0428239 s

method {:test} Test13() {
var r0 := Triple(2581);
expect r0 == 3 * 2581;
}

// REPEAT 9 - TIME: 8.5613142 s

method {:test} Test14() {
var r0 := Triple(2582);
expect r0 == 3 * 2582;
}

// REPEAT 10 - TIME: 8.9921933 s
