// dafny-synthesis_task_id_58.dfy

method {:testEntry} HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  result := a < 0 && b > 0;
}

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

// REPEAT 8 - TIME: 29.4281488 s
