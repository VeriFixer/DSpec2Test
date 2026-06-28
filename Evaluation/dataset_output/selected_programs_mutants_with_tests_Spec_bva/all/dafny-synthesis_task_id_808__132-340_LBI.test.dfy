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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 24];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test1() {
var seqint0 : seq<int> := [24];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [24, 0];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, -100];
var r0 := ContainsK(seqint0, -100);
expect r0 <==> -100 in seqint0;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 100];
var r0 := ContainsK(seqint0, 100);
expect r0 <==> 100 in seqint0;
}
method {:test} Test9() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test12() {
var seqint0 : seq<int> := [0, 0];
var r0 := ContainsK(seqint0, 24);
expect r0 <==> 24 in seqint0;
}
method {:test} Test13() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, -100);
expect r0 <==> -100 in seqint0;
}
method {:test} Test14() {
var seqint0 : seq<int> := [];
var r0 := ContainsK(seqint0, 100);
expect r0 <==> 100 in seqint0;
}

// REPEAT 1 - TIME: 14.4939929 s

method {:test} Test19() {
var seqint0 : seq<int> := [4, 25, 2];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}
method {:test} Test20() {
var seqint0 : seq<int> := [3, 1, 5];
var r0 := ContainsK(seqint0, 25);
expect r0 <==> 25 in seqint0;
}

// REPEAT 2 - TIME: 15.8751075 s

method {:test} Test21() {
var seqint0 : seq<int> := [9, 0, 7, 26];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}
method {:test} Test22() {
var seqint0 : seq<int> := [12, 0, 8, 0, 0, 0, 0, 6, 0, 10];
var r0 := ContainsK(seqint0, 26);
expect r0 <==> 26 in seqint0;
}

// REPEAT 3 - TIME: 17.2403055 s

method {:test} Test23() {
var seqint0 : seq<int> := [15, 13, 27, 0, 0];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}
method {:test} Test24() {
var seqint0 : seq<int> := [18, 0, 14, 0, 0, 0, 0, 0, 11, 16, 0];
var r0 := ContainsK(seqint0, 27);
expect r0 <==> 27 in seqint0;
}

// REPEAT 4 - TIME: 18.6326649 s

method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 28, 0, 21, 0, 23, 30, 19, 0, 0, 32];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}
method {:test} Test26() {
var seqint0 : seq<int> := [20, 0, 0, 0, 0, 0, 0, 0, 0, 29, 22, 17];
var r0 := ContainsK(seqint0, 28);
expect r0 <==> 28 in seqint0;
}

// REPEAT 5 - TIME: 19.9445483 s

method {:test} Test27() {
var seqint0 : seq<int> := [34, 31, 0, 0, 36, 38];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}
method {:test} Test28() {
var seqint0 : seq<int> := [39, 0, 0, 33, 35, 37];
var r0 := ContainsK(seqint0, 31);
expect r0 <==> 31 in seqint0;
}

// REPEAT 6 - TIME: 21.2935797 s

method {:test} Test29() {
var seqint0 : seq<int> := [46, 0, 0, 0, 0, 0, 0, 0, 42, 54, 44, 52, 0, 48, 56, 50, 0, 0, 40];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}
method {:test} Test30() {
var seqint0 : seq<int> := [53, 0, 43, 41, 0, 0, 0, 0, 49, 0, 47, 45, 51];
var r0 := ContainsK(seqint0, 40);
expect r0 <==> 40 in seqint0;
}

// REPEAT 7 - TIME: 22.6082602 s

method {:test} Test31() {
var seqint0 : seq<int> := [62, 0, 55, 58, 0, 0, 60];
var r0 := ContainsK(seqint0, 55);
expect r0 <==> 55 in seqint0;
}
method {:test} Test32() {
var seqint0 : seq<int> := [57, 0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 65, 0, 67, 63, 69];
var r0 := ContainsK(seqint0, 55);
expect r0 <==> 55 in seqint0;
}

// REPEAT 8 - TIME: 23.9184978 s

method {:test} Test33() {
var seqint0 : seq<int> := [68, 0, 0, 0, 0, 0, 0, 0, 64, 0, 71, 73, 0, 0, 75, 0, 0, 0, 77, 0, 0];
var r0 := ContainsK(seqint0, 64);
expect r0 <==> 64 in seqint0;
}
method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 70, 0, 76, 0, 0, 0, 74, 0, 78, 0, 80, 0, 82];
var r0 := ContainsK(seqint0, 64);
expect r0 <==> 64 in seqint0;
}

// REPEAT 9 - TIME: 25.5563541 s

method {:test} Test35() {
var seqint0 : seq<int> := [91, 0, 79, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 85, 89, 87];
var r0 := ContainsK(seqint0, 79);
expect r0 <==> 79 in seqint0;
}
method {:test} Test36() {
var seqint0 : seq<int> := [0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 88, 86, 0, 0, 92, 0, 84, 0, 90, 0, 94];
var r0 := ContainsK(seqint0, 79);
expect r0 <==> 79 in seqint0;
}

// REPEAT 10 - TIME: 27.2147932 s
