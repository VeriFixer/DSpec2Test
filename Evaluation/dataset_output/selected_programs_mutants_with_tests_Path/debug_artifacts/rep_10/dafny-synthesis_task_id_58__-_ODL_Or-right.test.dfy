// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0;
}

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

// REPEAT 10 - TIME: 28.2607123 s
