// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0 <==> a > 0 && b < 0;
}


method {:test} Test0() {
var r0 := HasOppositeSign(-1, 0);
expect r0 <==> (-1 < 0 && 0 > 0) || (-1 > 0 && 0 < 0);
}
method {:test} Test1() {
var r0 := HasOppositeSign(-1, 1);
expect r0 <==> (-1 < 0 && 1 > 0) || (-1 > 0 && 1 < 0);
}
method {:test} Test2() {
var r0 := HasOppositeSign(1, 0);
expect r0 <==> (1 < 0 && 0 > 0) || (1 > 0 && 0 < 0);
}
method {:test} Test3() {
var r0 := HasOppositeSign(0, 0);
expect r0 <==> (0 < 0 && 0 > 0) || (0 > 0 && 0 < 0);
}

// REPEAT 1 - TIME: 4.5549005 s

method {:test} Test4() {
var r0 := HasOppositeSign(-2, -1);
expect r0 <==> (-2 < 0 && -1 > 0) || (-2 > 0 && -1 < 0);
}
method {:test} Test5() {
var r0 := HasOppositeSign(-2, 2);
expect r0 <==> (-2 < 0 && 2 > 0) || (-2 > 0 && 2 < 0);
}
method {:test} Test6() {
var r0 := HasOppositeSign(2, 2);
expect r0 <==> (2 < 0 && 2 > 0) || (2 > 0 && 2 < 0);
}

// REPEAT 2 - TIME: 7.6188424 s

method {:test} Test7() {
var r0 := HasOppositeSign(-3, -2);
expect r0 <==> (-3 < 0 && -2 > 0) || (-3 > 0 && -2 < 0);
}
method {:test} Test8() {
var r0 := HasOppositeSign(-3, 3);
expect r0 <==> (-3 < 0 && 3 > 0) || (-3 > 0 && 3 < 0);
}
method {:test} Test9() {
var r0 := HasOppositeSign(3, 3);
expect r0 <==> (3 < 0 && 3 > 0) || (3 > 0 && 3 < 0);
}

// REPEAT 3 - TIME: 9.6879631 s

method {:test} Test10() {
var r0 := HasOppositeSign(-4, -3);
expect r0 <==> (-4 < 0 && -3 > 0) || (-4 > 0 && -3 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(-4, 4);
expect r0 <==> (-4 < 0 && 4 > 0) || (-4 > 0 && 4 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(4, 4);
expect r0 <==> (4 < 0 && 4 > 0) || (4 > 0 && 4 < 0);
}

// REPEAT 4 - TIME: 11.8756852 s

method {:test} Test13() {
var r0 := HasOppositeSign(-5, -4);
expect r0 <==> (-5 < 0 && -4 > 0) || (-5 > 0 && -4 < 0);
}
method {:test} Test14() {
var r0 := HasOppositeSign(-5, 5);
expect r0 <==> (-5 < 0 && 5 > 0) || (-5 > 0 && 5 < 0);
}
method {:test} Test15() {
var r0 := HasOppositeSign(5, 5);
expect r0 <==> (5 < 0 && 5 > 0) || (5 > 0 && 5 < 0);
}

// REPEAT 5 - TIME: 14.0394676 s

method {:test} Test16() {
var r0 := HasOppositeSign(-6, -5);
expect r0 <==> (-6 < 0 && -5 > 0) || (-6 > 0 && -5 < 0);
}
method {:test} Test17() {
var r0 := HasOppositeSign(-6, 6);
expect r0 <==> (-6 < 0 && 6 > 0) || (-6 > 0 && 6 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(6, 6);
expect r0 <==> (6 < 0 && 6 > 0) || (6 > 0 && 6 < 0);
}

// REPEAT 6 - TIME: 16.7674819 s

method {:test} Test19() {
var r0 := HasOppositeSign(-7, -6);
expect r0 <==> (-7 < 0 && -6 > 0) || (-7 > 0 && -6 < 0);
}
method {:test} Test20() {
var r0 := HasOppositeSign(-7, 7);
expect r0 <==> (-7 < 0 && 7 > 0) || (-7 > 0 && 7 < 0);
}
method {:test} Test21() {
var r0 := HasOppositeSign(7, 7);
expect r0 <==> (7 < 0 && 7 > 0) || (7 > 0 && 7 < 0);
}

// REPEAT 7 - TIME: 19.2663979 s

method {:test} Test22() {
var r0 := HasOppositeSign(-8, -7);
expect r0 <==> (-8 < 0 && -7 > 0) || (-8 > 0 && -7 < 0);
}
method {:test} Test23() {
var r0 := HasOppositeSign(-8, 8);
expect r0 <==> (-8 < 0 && 8 > 0) || (-8 > 0 && 8 < 0);
}
method {:test} Test24() {
var r0 := HasOppositeSign(8, 8);
expect r0 <==> (8 < 0 && 8 > 0) || (8 > 0 && 8 < 0);
}

// REPEAT 8 - TIME: 21.8999689 s

method {:test} Test25() {
var r0 := HasOppositeSign(-9, -8);
expect r0 <==> (-9 < 0 && -8 > 0) || (-9 > 0 && -8 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(-9, 9);
expect r0 <==> (-9 < 0 && 9 > 0) || (-9 > 0 && 9 < 0);
}
method {:test} Test27() {
var r0 := HasOppositeSign(9, 9);
expect r0 <==> (9 < 0 && 9 > 0) || (9 > 0 && 9 < 0);
}

// REPEAT 9 - TIME: 24.5941254 s

method {:test} Test28() {
var r0 := HasOppositeSign(-10, -9);
expect r0 <==> (-10 < 0 && -9 > 0) || (-10 > 0 && -9 < 0);
}
method {:test} Test29() {
var r0 := HasOppositeSign(-10, 10);
expect r0 <==> (-10 < 0 && 10 > 0) || (-10 > 0 && 10 < 0);
}
method {:test} Test30() {
var r0 := HasOppositeSign(10, 10);
expect r0 <==> (10 < 0 && 10 > 0) || (10 > 0 && 10 < 0);
}

// REPEAT 10 - TIME: 27.5624835 s
