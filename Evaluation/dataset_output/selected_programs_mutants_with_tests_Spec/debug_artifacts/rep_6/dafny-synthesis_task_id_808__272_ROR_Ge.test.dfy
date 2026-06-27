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

method {:test} Test10() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 13, 0, 0, 0, 0, 0, 0, 0, 29];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 14];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 6 - TIME: 9.578207 s
