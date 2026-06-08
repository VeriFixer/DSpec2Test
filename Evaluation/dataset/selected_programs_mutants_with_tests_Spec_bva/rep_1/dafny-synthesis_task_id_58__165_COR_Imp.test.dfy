// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0 ==> a > 0 && b < 0;
}

method {:test} Test0() {
var r0 := HasOppositeSign(-1, 1);
expect r0 <==> (-1 < 0 && 1 > 0) || (-1 > 0 && 1 < 0);
}
method {:test} Test1() {
var r0 := HasOppositeSign(-100, 1);
expect r0 <==> (-100 < 0 && 1 > 0) || (-100 > 0 && 1 < 0);
}
method {:test} Test4() {
var r0 := HasOppositeSign(-1, 100);
expect r0 <==> (-1 < 0 && 100 > 0) || (-1 > 0 && 100 < 0);
}
method {:test} Test9() {
var r0 := HasOppositeSign(1, -1);
expect r0 <==> (1 < 0 && -1 > 0) || (1 > 0 && -1 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(100, -1);
expect r0 <==> (100 < 0 && -1 > 0) || (100 > 0 && -1 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(1, -100);
expect r0 <==> (1 < 0 && -100 > 0) || (1 > 0 && -100 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(0, 0);
expect r0 <==> (0 < 0 && 0 > 0) || (0 > 0 && 0 < 0);
}
method {:test} Test19() {
var r0 := HasOppositeSign(0, -100);
expect r0 <==> (0 < 0 && -100 > 0) || (0 > 0 && -100 < 0);
}
method {:test} Test20() {
var r0 := HasOppositeSign(0, 100);
expect r0 <==> (0 < 0 && 100 > 0) || (0 > 0 && 100 < 0);
}
method {:test} Test25() {
var r0 := HasOppositeSign(1, 0);
expect r0 <==> (1 < 0 && 0 > 0) || (1 > 0 && 0 < 0);
}
method {:test} Test26() {
var r0 := HasOppositeSign(100, 0);
expect r0 <==> (100 < 0 && 0 > 0) || (100 > 0 && 0 < 0);
}
method {:test} Test28() {
var r0 := HasOppositeSign(1, 100);
expect r0 <==> (1 < 0 && 100 > 0) || (1 > 0 && 100 < 0);
}
method {:test} Test33() {
var r0 := HasOppositeSign(-1, 0);
expect r0 <==> (-1 < 0 && 0 > 0) || (-1 > 0 && 0 < 0);
}
method {:test} Test34() {
var r0 := HasOppositeSign(-100, 0);
expect r0 <==> (-100 < 0 && 0 > 0) || (-100 > 0 && 0 < 0);
}
method {:test} Test35() {
var r0 := HasOppositeSign(-1, -100);
expect r0 <==> (-1 < 0 && -100 > 0) || (-1 > 0 && -100 < 0);
}

// REPEAT 1 - TIME: 20.533178 s
