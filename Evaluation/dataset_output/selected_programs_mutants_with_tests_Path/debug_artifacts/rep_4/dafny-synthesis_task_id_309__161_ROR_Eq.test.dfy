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

method {:test} Test6() {
var r0 := Max(4, 4);
expect r0 == 4 || r0 == 4;
expect r0 >= 4 && r0 >= 4;
}
method {:test} Test7() {
var r0 := Max(4, 5);
expect r0 == 4 || r0 == 5;
expect r0 >= 4 && r0 >= 5;
}

// REPEAT 4 - TIME: 3.5731433 s
