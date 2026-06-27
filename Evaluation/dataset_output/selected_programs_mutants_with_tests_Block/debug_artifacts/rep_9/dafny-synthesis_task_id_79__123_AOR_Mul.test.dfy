// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| * 2 == 1;
}

method {:test} Test8() {
var r0 := IsLengthOdd("\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a");
expect r0 <==> |"\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| % 2 == 1;
}

// REPEAT 9 - TIME: 9.1387142 s
