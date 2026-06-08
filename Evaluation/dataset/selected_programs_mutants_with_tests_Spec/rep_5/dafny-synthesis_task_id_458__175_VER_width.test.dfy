// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := width * width;
}

method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(5, 5);
expect r0 == 5 * 5;
}

// REPEAT 5 - TIME: 6.0328224 s
