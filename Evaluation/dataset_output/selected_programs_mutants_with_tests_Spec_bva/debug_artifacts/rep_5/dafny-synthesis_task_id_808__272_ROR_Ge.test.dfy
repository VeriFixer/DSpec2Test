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

method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 28, 0, 21, 0, 23, 30, 19, 0, 0, 32];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}
method {:test} Test26() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 29, 22, 17];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 5 - TIME: 15.0662522 s
