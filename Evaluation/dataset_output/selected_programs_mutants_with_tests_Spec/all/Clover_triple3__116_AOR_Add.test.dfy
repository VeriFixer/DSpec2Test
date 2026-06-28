// Clover_triple3.dfy

method {:testEntry} Triple(x: int) returns (r: int)
  ensures r == 3 * x
{
  if x == 0 {
    r := 0;
  } else {
    var y := 2 + x;
    r := x + y;
  }
}


method {:test} Test0() {
var r0 := Triple(2573);
expect r0 == 3 * 2573;
}

// REPEAT 1 - TIME: 2.771227 s

method {:test} Test1() {
var r0 := Triple(2574);
expect r0 == 3 * 2574;
}

// REPEAT 2 - TIME: 3.6470221 s

method {:test} Test2() {
var r0 := Triple(2575);
expect r0 == 3 * 2575;
}

// REPEAT 3 - TIME: 4.5852586 s

method {:test} Test3() {
var r0 := Triple(2576);
expect r0 == 3 * 2576;
}

// REPEAT 4 - TIME: 5.5987038 s

method {:test} Test4() {
var r0 := Triple(2577);
expect r0 == 3 * 2577;
}

// REPEAT 5 - TIME: 6.4739008 s

method {:test} Test5() {
var r0 := Triple(2578);
expect r0 == 3 * 2578;
}

// REPEAT 6 - TIME: 7.4390706 s

method {:test} Test6() {
var r0 := Triple(2579);
expect r0 == 3 * 2579;
}

// REPEAT 7 - TIME: 8.4440571 s

method {:test} Test7() {
var r0 := Triple(2580);
expect r0 == 3 * 2580;
}

// REPEAT 8 - TIME: 9.3864412 s

method {:test} Test8() {
var r0 := Triple(2581);
expect r0 == 3 * 2581;
}

// REPEAT 9 - TIME: 10.2276449 s

method {:test} Test9() {
var r0 := Triple(2582);
expect r0 == 3 * 2582;
}

// REPEAT 10 - TIME: 11.1574322 s
