// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a > 0 && b < 0;
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

// REPEAT 1 - TIME: 4.3154951 s
