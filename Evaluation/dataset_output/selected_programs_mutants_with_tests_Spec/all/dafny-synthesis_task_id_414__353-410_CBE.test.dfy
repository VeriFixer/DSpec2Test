// dafny-synthesis_task_id_414.dfy

method {:testEntry} AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |seq1| && seq1[i] in seq2
{
  result := false;
  for i := 0 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result <==> exists k :: 0 <= k < i && seq1[k] in seq2
  {
    result := true;
    break;
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 1 - TIME: 3.3623818 s

method {:test} Test2() {
var seqint0 : seq<int> := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
var seqint1 : seq<int> := [1];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test3() {
var seqint0 : seq<int> := [3];
var seqint1 : seq<int> := [0, 0, 1];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 2 - TIME: 4.8589054 s

method {:test} Test4() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var seqint1 : seq<int> := [5, 2];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test5() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var seqint1 : seq<int> := [7, 5];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 3 - TIME: 6.438209 s

method {:test} Test6() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 4];
var seqint1 : seq<int> := [11, 4, 8];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test7() {
var seqint0 : seq<int> := [11, 0];
var seqint1 : seq<int> := [8, 0, 0, 4];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 4 - TIME: 8.0472957 s

method {:test} Test8() {
var seqint0 : seq<int> := [26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6];
var seqint1 : seq<int> := [6, 0, 0, 12, 20, 0, 0, 22, 0, 0, 18];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test9() {
var seqint0 : seq<int> := [20, 0, 6];
var seqint1 : seq<int> := [18, 0, 12, 16, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 5 - TIME: 9.5960862 s

method {:test} Test10() {
var seqint0 : seq<int> := [32, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 17, 0, 0, 0, 25, 0];
var seqint1 : seq<int> := [30, 10, 0, 28];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test11() {
var seqint0 : seq<int> := [34, 0, 0, 0, 0, 17, 0, 21, 0, 30];
var seqint1 : seq<int> := [32, 0, 0, 25, 28, 10];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 11.2691802 s

method {:test} Test12() {
var seqint0 : seq<int> := [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 33, 0, 14, 38, 0];
var seqint1 : seq<int> := [40, 0, 0, 0, 36, 23, 14];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test13() {
var seqint0 : seq<int> := [46, 23, 14, 33];
var seqint1 : seq<int> := [44, 0, 0, 0, 0, 38, 0, 29, 0, 36, 40, 42];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 7 - TIME: 12.856558 s

method {:test} Test14() {
var seqint0 : seq<int> := [50, 0, 0, 45, 19];
var seqint1 : seq<int> := [0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 19, 31, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 48, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test15() {
var seqint0 : seq<int> := [50, 0, 0, 41, 37];
var seqint1 : seq<int> := [48, 0, 0, 0, 0, 0, 19, 0, 0, 0, 45, 31, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 8 - TIME: 14.2692449 s

method {:test} Test16() {
var seqint0 : seq<int> := [65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 61, 59, 63];
var seqint1 : seq<int> := [0, 0, 0, 0, 47, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 51, 39, 0, 0, 0, 0, 53];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 39, 0, 0, 47, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 63, 0, 65];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 59, 0, 55, 0, 0, 0, 57, 51, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 9 - TIME: 15.5420632 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 54];
var seqint1 : seq<int> := [0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test19() {
var seqint0 : seq<int> := [70, 0, 0, 0, 0, 49, 0, 0, 0, 58, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 35, 0, 0, 0, 0, 0, 0, 0, 66, 0, 0, 0, 54, 68, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 10 - TIME: 16.966793 s
