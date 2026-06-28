// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  maxValue := b;
}

method {:test} Test18() {
var r0 := Max(13, 13);
expect r0 == 13 || r0 == 13;
expect r0 >= 13 && r0 >= 13;
}
method {:test} Test19() {
var r0 := Max(13, 14);
expect r0 == 13 || r0 == 14;
expect r0 >= 13 && r0 >= 14;
}

// REPEAT 10 - TIME: 13.5776129 s
