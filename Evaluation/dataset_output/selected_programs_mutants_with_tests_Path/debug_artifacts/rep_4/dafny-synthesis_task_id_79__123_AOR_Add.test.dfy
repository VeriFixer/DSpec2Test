// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| + 2 == 1;
}

method {:test} Test3() {
var r0 := IsLengthOdd("\0aaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 4 - TIME: 5.2819354 s
