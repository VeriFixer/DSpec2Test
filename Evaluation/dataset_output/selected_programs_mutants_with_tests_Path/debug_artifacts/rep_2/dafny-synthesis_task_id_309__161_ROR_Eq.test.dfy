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

method {:test} Test2() {
var r0 := Max(1, 1);
expect r0 == 1 || r0 == 1;
expect r0 >= 1 && r0 >= 1;
}
method {:test} Test3() {
var r0 := Max(1, 2);
expect r0 == 1 || r0 == 2;
expect r0 >= 1 && r0 >= 2;
}

// REPEAT 2 - TIME: 3.3374105 s
