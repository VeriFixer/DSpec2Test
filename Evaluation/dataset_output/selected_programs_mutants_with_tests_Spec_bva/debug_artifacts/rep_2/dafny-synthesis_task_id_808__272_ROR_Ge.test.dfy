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

method {:test} Test19() {
var seqint0 : seq<int> := [4, 25, 2];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}
method {:test} Test20() {
var seqint0 : seq<int> := [3, 1, 5];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}

// REPEAT 2 - TIME: 11.7946968 s
