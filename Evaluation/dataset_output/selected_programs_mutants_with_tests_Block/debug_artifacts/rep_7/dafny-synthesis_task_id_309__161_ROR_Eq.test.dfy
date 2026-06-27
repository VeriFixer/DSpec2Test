// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  if a == b {
    maxValue := a;
  } else {
    maxValue := b;
  }
}

method {:test} Test12() {
var r0 := Max(8, 9);
expect r0 == 8 || r0 == 9;
expect r0 >= 8 && r0 >= 9;
}
method {:test} Test13() {
var r0 := Max(9, 9);
expect r0 == 9 || r0 == 9;
expect r0 >= 9 && r0 >= 9;
}

// REPEAT 7 - TIME: 9.6127885 s
