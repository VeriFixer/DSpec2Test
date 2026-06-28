// dafny-synthesis_task_id_458.dfy

method {:testEntry} RectangleArea(length: int, width: int) returns (area: int)
  requires length > 0
  requires width > 0
  ensures area == length * width
{
  area := length * length;
}

method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(8, 8);
expect r0 == 8 * 8;
}

// REPEAT 8 - TIME: 10.4980721 s
