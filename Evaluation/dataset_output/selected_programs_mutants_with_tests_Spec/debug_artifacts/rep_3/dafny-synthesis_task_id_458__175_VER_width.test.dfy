// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := width * width;
}

method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 4.6002664 s
