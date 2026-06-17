// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := -(a * b);
}


method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a * b;
}

method {:test} Test0() {
var r0 := Multiply(0, 7719);
expect r0 == 0 * 7719;
}

// REPEAT 1 - TIME: 4.268126 s

method {:test} Test1() {
var r0 := Multiply(1, 7720);
expect r0 == 1 * 7720;
}

// REPEAT 2 - TIME: 5.6278142 s

method {:test} Test2() {
var r0 := Multiply(7721, 7721);
expect r0 == 7721 * 7721;
}

// REPEAT 3 - TIME: 7.023987 s

method {:test} Test3() {
var r0 := Multiply(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 4 - TIME: 8.5004382 s

method {:test} Test4() {
var r0 := Multiply(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 5 - TIME: 9.8838446 s

method {:test} Test5() {
var r0 := Multiply(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 6 - TIME: 10.9144482 s

method {:test} Test6() {
var r0 := Multiply(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 7 - TIME: 11.7162379 s

method {:test} Test7() {
var r0 := Multiply(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 8 - TIME: 12.6821791 s

method {:test} Test8() {
var r0 := Multiply(7727, 7727);
expect r0 == 7727 * 7727;
}

// REPEAT 9 - TIME: 13.7538006 s

method {:test} Test9() {
var r0 := Multiply(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 10 - TIME: 14.7571254 s
