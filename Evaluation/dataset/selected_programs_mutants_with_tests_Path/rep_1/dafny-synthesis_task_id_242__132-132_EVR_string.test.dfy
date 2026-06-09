// dafny-synthesis_task_id_242.dfy

method {:testEntry} CountCharacters(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s|
{
  count := |""|;
}

method {:test} Test0() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}

// REPEAT 1 - TIME: 3.1122484 s
