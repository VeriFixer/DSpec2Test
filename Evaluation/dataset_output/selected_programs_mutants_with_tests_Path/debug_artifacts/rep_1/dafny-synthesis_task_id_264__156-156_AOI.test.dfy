// dafny-synthesis_task_id_264.dfy

method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
  requires humanYears >= 0
  ensures dogYears == 7 * humanYears
{
  dogYears := -7 * humanYears;
}

method {:test} Test0() {
expect 38 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := DogYears(38);
expect r0 == 7 * 38;
}

// REPEAT 1 - TIME: 1.1400861 s
