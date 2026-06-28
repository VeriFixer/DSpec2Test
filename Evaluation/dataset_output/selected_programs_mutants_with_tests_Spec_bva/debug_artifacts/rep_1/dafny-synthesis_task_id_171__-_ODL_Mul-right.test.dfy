// dafny-synthesis_task_id_171.dfy

method {:testEntry} PentagonPerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 5 * side
{
  perimeter := 5;
}

method {:test} Test0() {
expect 1 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(1);
expect r0 == 5 * 1;
}
method {:test} Test2() {
expect 100 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(100);
expect r0 == 5 * 100;
}

// REPEAT 1 - TIME: 6.5936663 s
