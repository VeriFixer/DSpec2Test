// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    break;
    if s[i] == k {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 26];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 1 - TIME: 2.8815306 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 29];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 2 - TIME: 3.9199889 s

method {:test} Test2() {
var seqint0 : seq<int> := [40, 27];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 3 - TIME: 4.8330551 s

method {:test} Test3() {
var seqint0 : seq<int> := [44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 28];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 4 - TIME: 5.7432561 s

method {:test} Test4() {
var seqint0 : seq<int> := [64, 65];
var r0 := ContainsK(seqint0, 65);
expect r0 <==> 65 in seqint0;
}

// REPEAT 5 - TIME: 6.6655782 s

method {:test} Test5() {
var seqint0 : seq<int> := [69, 30, 0];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 6 - TIME: 7.5933991 s

method {:test} Test6() {
var seqint0 : seq<int> := [72];
var r0 := ContainsK(seqint0, 72);
expect r0 <==> 72 in seqint0;
}

// REPEAT 7 - TIME: 8.4047203 s

method {:test} Test7() {
var seqint0 : seq<int> := [31, 2, 0, 0, 0, 0, 0, 4];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 8 - TIME: 9.3001134 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 34];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}

// REPEAT 9 - TIME: 10.0803738 s

method {:test} Test9() {
var seqint0 : seq<int> := [106, 104, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 108, 35, 0, 0, 0, 0, 0, 0, 0, 0, 110];
var r0 := ContainsK(seqint0, 35);
expect r0 <==> 35 in seqint0;
}

// REPEAT 10 - TIME: 10.9158487 s
