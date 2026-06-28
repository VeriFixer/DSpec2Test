// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := false;
}

method {:test} Test5() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 6 - TIME: 6.8618525 s
