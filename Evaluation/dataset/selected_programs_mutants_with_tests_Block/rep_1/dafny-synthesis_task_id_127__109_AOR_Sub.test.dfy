// dafny-synthesis_task_id_127.dfy

method {:testEntry} Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  result := a - b;
}

method {:test} Test0() {
var r0 := Multiply(0, 7719);
expect r0 == 0 * 7719;
}

// REPEAT 1 - TIME: 1.9833891 s
