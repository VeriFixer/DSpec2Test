// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := 0;
}

method {:test} Test0() {
var r0 := Multiply(7719, 0);
expect r0 == 7719 * 0;
}

// REPEAT 1 - TIME: 2.5091246 s
