// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] <= k {
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

// REPEAT 1 - TIME: 10.1359045 s

method {:test} Test2() {
var seqint0 : seq<int> := [0];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 2 - TIME: 18.2337152 s

method {:test} Test4() {
var seqint0 : seq<int> := [54, 52];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [55, 53, 31];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 3 - TIME: 26.0427125 s

method {:test} Test6() {
var seqint0 : seq<int> := [64, 62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66];
var r0 := ContainsK(seqint0, 33);
expect r0 <==> 33 in seqint0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 0, 69, 0, 0, 0, 0, 34];
var r0 := ContainsK(seqint0, 34);
expect r0 <==> 34 in seqint0;
}

// REPEAT 4 - TIME: 34.8761076 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 108, 107, 109];
var r0 := ContainsK(seqint0, 32);
expect r0 <==> 32 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 108, 32, 0, 0, 0, 0, 0, 0, 0, 5, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112];
var r0 := ContainsK(seqint0, 32);
expect r0 <==> 32 in seqint0;
}

// REPEAT 5 - TIME: 47.3529754 s

method {:test} Test10() {
var seqint0 : seq<int> := [159, 155, 156, 0, 0, 0, 157, 0, 0, 158];
var r0 := ContainsK(seqint0, 38);
expect r0 <==> 38 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 156, 157, 0, 0, 0, 0, 0, 0, 0, 0, 0, 160, 162, 0, 35, 159, 0, 0, 0, 0, 0, 158, 0, 0, 0, 163];
var r0 := ContainsK(seqint0, 35);
expect r0 <==> 35 in seqint0;
}

// REPEAT 6 - TIME: 59.0356351 s

method {:test} Test12() {
var seqint0 : seq<int> := [209, 200, 201, 0, 0, 0, 0, 0, 0, 0, 0, 0, 206, 207, 203, 0, 0, 0, 0, 205, 0, 202, 208];
var r0 := ContainsK(seqint0, 36);
expect r0 <==> 36 in seqint0;
}
method {:test} Test13() {
var seqint0 : seq<int> := [213, 203, 205, 0, 0, 0, 0, 0, 0, 206, 36, 0, 0, 0];
var r0 := ContainsK(seqint0, 36);
expect r0 <==> 36 in seqint0;
}

// REPEAT 7 - TIME: 68.7629215 s

method {:test} Test14() {
var seqint0 : seq<int> := [250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 249];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}
method {:test} Test15() {
var seqint0 : seq<int> := [251, 0, 0, 0, 0, 0, 0, 0, 41, 0, 249];
var r0 := ContainsK(seqint0, 41);
expect r0 <==> 41 in seqint0;
}

// REPEAT 8 - TIME: 81.025147 s

method {:test} Test16() {
var seqint0 : seq<int> := [280, 0, 270, 0, 0, 0, 0, 0, 0, 0, 0, 0, 274, 275, 276, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 278, 279, 0, 272];
var r0 := ContainsK(seqint0, 42);
expect r0 <==> 42 in seqint0;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := ContainsK(seqint0, 39);
expect r0 <==> 39 in seqint0;
}

// REPEAT 9 - TIME: 95.1868507 s

method {:test} Test18() {
var seqint0 : seq<int> := [343, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 340, 341, 337, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := ContainsK(seqint0, 44);
expect r0 <==> 44 in seqint0;
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := ContainsK(seqint0, 43);
expect r0 <==> 43 in seqint0;
}

// REPEAT 10 - TIME: 111.5289351 s
