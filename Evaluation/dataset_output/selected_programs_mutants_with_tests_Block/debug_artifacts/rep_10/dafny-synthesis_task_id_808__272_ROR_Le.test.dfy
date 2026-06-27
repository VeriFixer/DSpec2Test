// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] <= k {
      result := true;
      break;
    }
  }
}

method {:test} Test9() {
var seqint0 : seq<int> := [106, 104, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 108, 35, 0, 0, 0, 0, 0, 0, 0, 0, 110];
var r0 := ContainsK(seqint0, 35);
expect r0 <==> 35 in seqint0;
}

// REPEAT 10 - TIME: 10.9158487 s
