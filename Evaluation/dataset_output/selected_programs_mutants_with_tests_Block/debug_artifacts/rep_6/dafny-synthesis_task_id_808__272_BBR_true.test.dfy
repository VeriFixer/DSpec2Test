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

method {:test} Test5() {
var seqint0 : seq<int> := [72];
var r0 := ContainsK(seqint0, 72);
expect r0 <==> 72 in seqint0;
}

// REPEAT 6 - TIME: 7.748262 s
