// dafny-synthesis_task_id_626.dfy

method {:testEntry} AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
{
  area := -radius * radius;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(1);
expect r0 == 1 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(100);
expect r0 == 100 * 100;
}
method {:test} Test4() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(10);
expect r0 == 10 * 10;
}

// REPEAT 1 - TIME: 5.9371851 s
