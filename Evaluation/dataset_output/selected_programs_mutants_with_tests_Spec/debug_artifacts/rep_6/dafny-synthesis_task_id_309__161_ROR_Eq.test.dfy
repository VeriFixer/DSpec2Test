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

method {:test} Test10() {
var r0 := Max(7, 7);
expect r0 == 7 || r0 == 7;
expect r0 >= 7 && r0 >= 7;
}
method {:test} Test11() {
var r0 := Max(7, 8);
expect r0 == 7 || r0 == 8;
expect r0 >= 7 && r0 >= 8;
}

// REPEAT 6 - TIME: 9.668477 s
