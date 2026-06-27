// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := |s| - 2 == 1;
}

method {:test} Test0() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaa"| % 2 == 1;
}
method {:test} Test1() {
var r0 := IsLengthOdd("aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| % 2 == 1;
}

// REPEAT 1 - TIME: 3.3367541 s
