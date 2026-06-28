// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] != k {
      result := true;
      break;
    }
  }
}

method {:test} Test3() {
var seqint0 : seq<int> := [45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 29];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 4 - TIME: 5.6497094 s
