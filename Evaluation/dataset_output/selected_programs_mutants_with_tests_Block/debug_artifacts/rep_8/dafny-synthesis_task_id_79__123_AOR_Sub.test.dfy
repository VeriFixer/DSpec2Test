// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| - 2 == 1;
}

method {:test} Test7() {
var r0 := IsLengthOdd("\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"\0aaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 8 - TIME: 8.429119 s
