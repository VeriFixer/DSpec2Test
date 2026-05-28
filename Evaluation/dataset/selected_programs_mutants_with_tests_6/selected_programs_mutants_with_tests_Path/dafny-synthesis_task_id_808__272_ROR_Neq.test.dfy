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
method {:test} Test8() {
var seqint0 : seq<int> := [182, 180, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181];
var r0 := ContainsK(seqint0, 47);
expect r0 <==> 47 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [184, 177, 0, 0, 0, 0, 180, 0, 0, 44, 0, 0, 181];
var r0 := ContainsK(seqint0, 44);
expect r0 <==> 44 in seqint0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 214, 216, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 217];
var r0 := ContainsK(seqint0, 51);
expect r0 <==> 51 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [217, 211, 0, 214, 0, 0, 0, 0, 0, 0, 45, 0, 215, 0];
var r0 := ContainsK(seqint0, 45);
expect r0 <==> 45 in seqint0;
}
