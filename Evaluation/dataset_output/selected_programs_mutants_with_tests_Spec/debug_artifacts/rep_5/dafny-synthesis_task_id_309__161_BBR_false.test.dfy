// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  if false {
    maxValue := a;
  } else {
    maxValue := b;
  }
}

method {:test} Test8() {
var r0 := Max(6, 6);
expect r0 == 6 || r0 == 6;
expect r0 >= 6 && r0 >= 6;
}
method {:test} Test9() {
var r0 := Max(5, 6);
expect r0 == 5 || r0 == 6;
expect r0 >= 5 && r0 >= 6;
}

// REPEAT 5 - TIME: 8.0780251 s
