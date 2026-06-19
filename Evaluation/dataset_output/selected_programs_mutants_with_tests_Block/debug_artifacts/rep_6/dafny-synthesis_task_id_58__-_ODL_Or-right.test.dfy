// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0;
}

method {:test} Test17() {
var r0 := HasOppositeSign(-6, -5);
expect r0 <==> (-6 < 0 && -5 > 0) || (-6 > 0 && -5 < 0);
}
method {:test} Test18() {
var r0 := HasOppositeSign(-6, 6);
expect r0 <==> (-6 < 0 && 6 > 0) || (-6 > 0 && 6 < 0);
}
method {:test} Test19() {
var r0 := HasOppositeSign(6, -5);
expect r0 <==> (6 < 0 && -5 > 0) || (6 > 0 && -5 < 0);
}

// REPEAT 6 - TIME: 11.3966332 s
