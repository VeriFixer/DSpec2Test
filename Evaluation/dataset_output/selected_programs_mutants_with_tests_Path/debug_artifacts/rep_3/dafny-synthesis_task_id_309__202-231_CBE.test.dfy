// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  maxValue := b;
}

method {:test} Test4() {
var r0 := Max(3, 3);
expect r0 == 3 || r0 == 3;
expect r0 >= 3 && r0 >= 3;
}
method {:test} Test5() {
var r0 := Max(2, 3);
expect r0 == 2 || r0 == 3;
expect r0 >= 2 && r0 >= 3;
}

// REPEAT 3 - TIME: 7.697484 s
