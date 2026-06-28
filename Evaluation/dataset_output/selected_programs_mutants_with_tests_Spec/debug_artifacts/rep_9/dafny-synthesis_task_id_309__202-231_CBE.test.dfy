// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  maxValue := b;
}

method {:test} Test16() {
var r0 := Max(12, 12);
expect r0 == 12 || r0 == 12;
expect r0 >= 12 && r0 >= 12;
}
method {:test} Test17() {
var r0 := Max(11, 12);
expect r0 == 11 || r0 == 12;
expect r0 >= 11 && r0 >= 12;
}

// REPEAT 9 - TIME: 12.5047678 s
