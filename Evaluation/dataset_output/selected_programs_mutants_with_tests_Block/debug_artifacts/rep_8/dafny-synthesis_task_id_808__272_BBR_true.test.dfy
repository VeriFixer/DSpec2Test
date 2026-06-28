// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if true {
      result := true;
      break;
    }
  }
}

method {:test} Test7() {
var seqint0 : seq<int> := [30, 3, 0, 0, 0, 0, 0, 8, 0, 6, 0, 0, 0, 0, 0, 0, 0, 10];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 8 - TIME: 9.5090156 s
