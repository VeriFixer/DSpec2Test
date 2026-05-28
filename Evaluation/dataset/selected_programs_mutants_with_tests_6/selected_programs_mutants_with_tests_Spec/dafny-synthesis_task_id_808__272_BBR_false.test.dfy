// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if false {
      result := true;
      break;
    }
  }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [40];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [2, 41];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 1];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}
method {:test} Test6() {
var seqint0 : seq<int> := [6, 42, 4];
var r0 := ContainsK(seqint0, 42);
expect r0 <==> 42 in seqint0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [5, 3, 0];
var r0 := ContainsK(seqint0, 42);
expect r0 <==> 42 in seqint0;
}
method {:test} Test8() {
var seqint0 : seq<int> := [43, 0, 0];
var r0 := ContainsK(seqint0, 43);
expect r0 <==> 43 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [13, 7, 9, 11];
var r0 := ContainsK(seqint0, 43);
expect r0 <==> 43 in seqint0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [14, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 20];
var r0 := ContainsK(seqint0, 44);
expect r0 <==> 44 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [17, 8, 12, 15];
var r0 := ContainsK(seqint0, 44);
expect r0 <==> 44 in seqint0;
}
