// dafny-synthesis_task_id_264.dfy

method {:testEntry} DogYears(humanYears: int) returns (dogYears: int)
  requires humanYears >= 0
  ensures dogYears == 7 * humanYears
{
  dogYears := -(7 * humanYears);
}
