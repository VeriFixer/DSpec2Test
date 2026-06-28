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

method {:test} Test6() {
var seqint0 : seq<int> := [73, 67, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 0, 0, 0, 70];
var r0 := ContainsK(seqint0, 32);
expect r0 <==> 32 in seqint0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [72, 29, 70];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 4 - TIME: 43.3408692 s
