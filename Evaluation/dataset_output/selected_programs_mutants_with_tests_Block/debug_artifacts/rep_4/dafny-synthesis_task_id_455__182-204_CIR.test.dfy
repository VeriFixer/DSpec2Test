// dafny-synthesis_task_id_455.dfy

method {:testEntry} MonthHas31Days(month: int) returns (result: bool)
  requires 1 <= month <= 12
  ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
  result := month in {};
}

method {:test} Test3() {
expect 1 <= 12 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(12);
expect r0 <==> 12 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 4 - TIME: 4.0385687 s
