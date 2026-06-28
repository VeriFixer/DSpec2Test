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

method {:test} Test9() {
var seqint0 : seq<int> := [123, 113, 0, 0, 0, 0, 0, 117, 0, 114, 0, 0, 0, 0, 0, 0, 0, 34, 118];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}

// REPEAT 10 - TIME: 11.0983166 s
