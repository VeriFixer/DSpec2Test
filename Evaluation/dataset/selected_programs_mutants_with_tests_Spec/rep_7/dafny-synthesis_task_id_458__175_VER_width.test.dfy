// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := width * width;
}

method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 7.3083485 s
