// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] < k {
      result := true;
      break;
    }
  }
}

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 27];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 2 - TIME: 3.7717617 s
