// dafny-synthesis_task_id_79.dfy

method {:testEntry} IsLengthOdd(s: string) returns (result: bool)
  ensures result <==> |s| % 2 == 1
{
  result := false;
}

method {:test} Test4() {
var r0 := IsLengthOdd("\0a");
expect r0 <==> |"\0a"| % 2 == 1;
}

// REPEAT 5 - TIME: 5.5419505 s
