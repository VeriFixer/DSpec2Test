// dafny-synthesis_task_id_455.dfy

method {:testEntry} MonthHas31Days(month: int) returns (result: bool)
  requires 1 <= month <= 12
  ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
  result := month in {1, 4, 5, 7, 8, 10, 12};
}

method {:test} Test4() {
expect 1 <= 6 <= 12, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MonthHas31Days(6);
expect r0 <==> 6 in {1, 3, 5, 7, 8, 10, 12};
}

// REPEAT 5 - TIME: 7.4330535 s
