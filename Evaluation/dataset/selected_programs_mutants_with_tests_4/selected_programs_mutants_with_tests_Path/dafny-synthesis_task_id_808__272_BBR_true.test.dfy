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

method {:test} Test0() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 0);
expect r0 <==> 0 in seqint0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [77];
var r0 := ContainsK(seqint0, 42);
expect r0 <==> 42 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [40];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [87, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84];
var r0 := ContainsK(seqint0, 43);
expect r0 <==> 43 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [85, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 81];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [143, 142, 0, 140, 0, 0, 0, 0, 0, 0, 0, 138];
var r0 := ContainsK(seqint0, 46);
expect r0 <==> 46 in seqint0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [141, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 139, 0, 0, 0, 0, 0, 0, 0, 0, 137];
var r0 := ContainsK(seqint0, 46);
expect r0 <==> 46 in seqint0;
}
