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
var seqint0 : seq<int> := [54, 52];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [55, 53, 31];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 3 - TIME: 26.0427125 s
