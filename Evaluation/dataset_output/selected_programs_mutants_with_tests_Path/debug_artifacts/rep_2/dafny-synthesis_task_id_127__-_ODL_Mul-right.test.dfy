// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a;
}

method {:test} Test1() {
var r0 := Multiply(1, 7720);
expect r0 == 1 * 7720;
}

// REPEAT 2 - TIME: 6.0356449 s
