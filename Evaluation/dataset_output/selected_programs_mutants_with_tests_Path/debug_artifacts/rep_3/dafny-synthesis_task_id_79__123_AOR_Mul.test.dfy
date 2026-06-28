// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| * 2 == 1;
}

method {:test} Test2() {
var r0 := IsLengthOdd("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| % 2 == 1;
}

// REPEAT 3 - TIME: 4.2964416 s
