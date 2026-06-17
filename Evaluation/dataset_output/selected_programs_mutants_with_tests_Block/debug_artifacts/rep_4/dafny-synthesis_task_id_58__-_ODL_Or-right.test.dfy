// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0;
}

method {:test} Test10() {
var r0 := HasOppositeSign(4, 4);
expect r0 <==> (4 < 0 && 4 > 0) || (4 > 0 && 4 < 0);
}
method {:test} Test11() {
var r0 := HasOppositeSign(-4, 4);
expect r0 <==> (-4 < 0 && 4 > 0) || (-4 > 0 && 4 < 0);
}
method {:test} Test12() {
var r0 := HasOppositeSign(-4, -3);
expect r0 <==> (-4 < 0 && -3 > 0) || (-4 > 0 && -3 < 0);
}

// REPEAT 4 - TIME: 8.2856615 s
