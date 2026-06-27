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

method {:test} Test14() {
var r0 := Max(10, 10);
expect r0 == 10 || r0 == 10;
expect r0 >= 10 && r0 >= 10;
}
method {:test} Test15() {
var r0 := Max(10, 11);
expect r0 == 10 || r0 == 11;
expect r0 >= 10 && r0 >= 11;
}

// REPEAT 8 - TIME: 12.0406589 s
