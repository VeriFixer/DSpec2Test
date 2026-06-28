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
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 0);
expect r0 <==> 0 in seqint0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 26];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 1 - TIME: 9.2463856 s

method {:test} Test2() {
var seqint0 : seq<int> := [38];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 2 - TIME: 18.7193377 s

method {:test} Test4() {
var seqint0 : seq<int> := [65, 63];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [30, 59];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 3 - TIME: 30.6526079 s

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

method {:test} Test8() {
var seqint0 : seq<int> := [110, 111, 0, 0, 0, 0, 0, 0, 108, 0, 0, 0, 112];
var r0 := ContainsK(seqint0, 33);
expect r0 <==> 33 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [31, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 5 - TIME: 56.0871904 s

method {:test} Test10() {
var seqint0 : seq<int> := [151, 152, 0, 0, 0, 0, 148];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [158, 146, 0, 149, 0, 0, 0, 0, 0, 0, 34, 150, 148, 151];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}

// REPEAT 6 - TIME: 65.9273647 s

method {:test} Test12() {
var seqint0 : seq<int> := [184, 178, 174, 176];
var r0 := ContainsK(seqint0, 35);
expect r0 <==> 35 in seqint0;
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 174, 35, 0, 0, 0, 0, 0, 0, 0, 178, 0, 0, 11, 0, 0, 0, 0, 0, 176, 0, 0, 0, 180, 9, 0, 0, 0, 13];
var r0 := ContainsK(seqint0, 35);
expect r0 <==> 35 in seqint0;
}

// REPEAT 7 - TIME: 76.650935 s

method {:test} Test14() {
var seqint0 : seq<int> := [220, 209, 211, 213, 215];
var r0 := ContainsK(seqint0, 36);
expect r0 <==> 36 in seqint0;
}
method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 214, 0, 0, 0, 0, 213, 0, 0, 0, 211, 0, 0, 209, 0, 218, 215];
var r0 := ContainsK(seqint0, 36);
expect r0 <==> 36 in seqint0;
}

// REPEAT 8 - TIME: 91.0011229 s

method {:test} Test16() {
var seqint0 : seq<int> := [249, 0, 0, 0, 244, 0];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}
method {:test} Test17() {
var seqint0 : seq<int> := [255, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244, 0, 247];
var r0 := ContainsK(seqint0, 37);
expect r0 <==> 37 in seqint0;
}

// REPEAT 9 - TIME: 106.3026562 s

method {:test} Test18() {
var seqint0 : seq<int> := [294, 0, 0, 0, 0, 0, 0, 289, 0, 285, 0, 0, 0, 291, 292];
var r0 := ContainsK(seqint0, 43);
expect r0 <==> 43 in seqint0;
}
method {:test} Test19() {
var seqint0 : seq<int> := [40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 292, 0, 0, 287, 0, 0, 0, 0, 285, 15, 0, 0, 12, 17, 0];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}

// REPEAT 10 - TIME: 122.4571792 s
