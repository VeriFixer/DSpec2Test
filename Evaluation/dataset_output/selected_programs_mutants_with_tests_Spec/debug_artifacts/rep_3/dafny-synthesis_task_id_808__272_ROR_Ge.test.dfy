// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] >= k {
      result := true;
      break;
    }
  }
}

method {:test} Test4() {
var seqint0 : seq<int> := [26, 3];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 3 - TIME: 5.8249863 s
