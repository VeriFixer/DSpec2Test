// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| / 2 == 1;
}

method {:test} Test8() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 9 - TIME: 9.3461776 s
