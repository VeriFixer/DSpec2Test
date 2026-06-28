// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if true {
      result := true;
      break;
    }
  }
}

method {:test} Test8() {
var seqint0 : seq<int> := [0, 112, 0, 0, 31, 108];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 9 - TIME: 10.2628782 s
