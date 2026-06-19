// dafny-synthesis_task_id_404.dfy

method {:testEntry} Min(a: int, b: int) returns (minValue: int)
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
{
  minValue := b;
}

method {:test} Test16() {
var r0 := Min(12, 12);
expect r0 == 12 || r0 == 12;
expect r0 <= 12 && r0 <= 12;
}
method {:test} Test17() {
var r0 := Min(13, 12);
expect r0 == 13 || r0 == 12;
expect r0 <= 13 && r0 <= 12;
}

// REPEAT 9 - TIME: 11.6992043 s
