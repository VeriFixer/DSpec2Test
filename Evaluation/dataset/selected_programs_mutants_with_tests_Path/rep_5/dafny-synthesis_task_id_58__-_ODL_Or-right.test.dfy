// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0;
}

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

// REPEAT 5 - TIME: 19.2901044 s
