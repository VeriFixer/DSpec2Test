// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| * 2 == 1;
}

method {:test} Test6() {
var r0 := IsLengthOdd("\U{0002}aa\0");
expect r0 <==> |"\U{0002}aa\0"| % 2 == 1;
}

// REPEAT 7 - TIME: 7.0312565 s
