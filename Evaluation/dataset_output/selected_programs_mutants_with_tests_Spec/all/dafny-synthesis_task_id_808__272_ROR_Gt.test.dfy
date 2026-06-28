// dafny-synthesis_task_id_808.dfy

method {:testEntry} ContainsK(s: seq<int>, k: int) returns (result: bool)
  ensures result <==> k in s
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists j :: 0 <= j < i && s[j] == k
  {
    if s[i] > k {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 24];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}

// REPEAT 1 - TIME: 3.1302542 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 25];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [1];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}

// REPEAT 2 - TIME: 4.4778085 s

method {:test} Test4() {
var seqint0 : seq<int> := [26, 3];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 3 - TIME: 5.8249863 s

method {:test} Test6() {
var seqint0 : seq<int> := [27, 5];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [4, 0];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 4 - TIME: 7.4427452 s

method {:test} Test8() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [8, 6, 0];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 5 - TIME: 8.8772154 s

method {:test} Test10() {
var seqint0 : seq<int> := [11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 13, 0, 0, 0, 0, 0, 0, 0, 29];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 14];
var r0 := ContainsK(seqint0, 29);
expect r0 <==> 29 in seqint0;
}

// REPEAT 6 - TIME: 10.4350929 s

method {:test} Test12() {
var seqint0 : seq<int> := [21, 30, 19, 17];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}
method {:test} Test13() {
var seqint0 : seq<int> := [18, 16, 0];
var r0 := ContainsK(seqint0, 30);
expect r0 <==> 30 in seqint0;
}

// REPEAT 7 - TIME: 11.6102919 s

method {:test} Test14() {
var seqint0 : seq<int> := [36, 0, 22, 0, 0, 0, 0, 31, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}
method {:test} Test15() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 35, 0, 37, 39, 0, 0, 0, 0, 41, 23];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 8 - TIME: 12.6275925 s

method {:test} Test16() {
var seqint0 : seq<int> := [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 46, 0, 0, 0, 38, 0, 0, 0, 48, 50, 52];
var r0 := ContainsK(seqint0, 38);
expect r0 <==> 38 in seqint0;
}
method {:test} Test17() {
var seqint0 : seq<int> := [45, 0, 0, 40, 43];
var r0 := ContainsK(seqint0, 38);
expect r0 <==> 38 in seqint0;
}

// REPEAT 9 - TIME: 13.8685877 s

method {:test} Test18() {
var seqint0 : seq<int> := [47, 51, 0, 0, 56, 58, 0, 60, 54, 62];
var r0 := ContainsK(seqint0, 47);
expect r0 <==> 47 in seqint0;
}
method {:test} Test19() {
var seqint0 : seq<int> := [55, 0, 53, 57, 0, 49, 0, 59, 0, 61];
var r0 := ContainsK(seqint0, 47);
expect r0 <==> 47 in seqint0;
}

// REPEAT 10 - TIME: 15.0461841 s
