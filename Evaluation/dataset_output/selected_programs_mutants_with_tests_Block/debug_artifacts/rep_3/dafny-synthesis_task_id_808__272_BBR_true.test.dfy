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

method {:test} Test2() {
var seqint0 : seq<int> := [28, 39];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 3 - TIME: 4.7730253 s
