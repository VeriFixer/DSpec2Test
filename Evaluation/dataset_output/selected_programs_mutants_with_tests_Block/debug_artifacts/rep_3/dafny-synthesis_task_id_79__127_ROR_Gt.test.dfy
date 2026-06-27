// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| % 2 > 1;
}

method {:test} Test2() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 3 - TIME: 4.2690341 s
