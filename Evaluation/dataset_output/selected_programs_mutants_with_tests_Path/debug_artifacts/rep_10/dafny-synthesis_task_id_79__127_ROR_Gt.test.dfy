// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| % 2 > 1;
}

method {:test} Test9() {
var r0 := IsLengthOdd("\U{0002}aaa\0aaa");
expect r0 <==> |"\U{0002}aaa\0aaa"| % 2 == 1;
}

// REPEAT 10 - TIME: 10.1341287 s
