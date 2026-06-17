// dafny-synthesis_task_id_309.dfy

method {:testEntry} Max(a: int, b: int) returns (maxValue: int)
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
{
  if true {
    maxValue := a;
  } else {
    maxValue := b;
  }
}

method {:test} Test0() {
var r0 := Max(0, 0);
expect r0 == 0 || r0 == 0;
expect r0 >= 0 && r0 >= 0;
}
method {:test} Test1() {
var r0 := Max(-1, 0);
expect r0 == -1 || r0 == 0;
expect r0 >= -1 && r0 >= 0;
}

// REPEAT 1 - TIME: 2.9419014 s
