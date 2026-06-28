// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| * 2 == 1;
}

method {:test} Test6() {
var r0 := IsLengthOdd("\0aaaaa");
expect r0 <==> |"\0aaaaa"| % 2 == 1;
}

// REPEAT 7 - TIME: 7.6505293 s
