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

method {:test} Test12() {
var seqint0 : seq<int> := [21, 30, 19, 17];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}
method {:test} Test13() {
var seqint0 : seq<int> := [18, 16, 0];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 7 - TIME: 10.6710037 s
