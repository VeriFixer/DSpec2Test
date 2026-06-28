// dafny-synthesis_task_id_414.dfy

method {:testEntry} AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |seq1| && seq1[i] in seq2
{
  result := false;
  for i := 1 to |seq1|
    invariant 0 <= i <= |seq1|
    invariant result <==> exists k :: 0 <= k < i && seq1[k] in seq2
  {
    if seq1[i] in seq2 {
      result := true;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test1() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test9() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test11() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test12() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test14() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test15() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 1 - TIME: 16.4087307 s

method {:test} Test20() {
var seqint0 : seq<int> := [3, 5, 9];
var seqint1 : seq<int> := [1, 3, 7];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test21() {
var seqint0 : seq<int> := [5, 1, 0];
var seqint1 : seq<int> := [7, 0, 3];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 2 - TIME: 17.9187077 s

method {:test} Test22() {
var seqint0 : seq<int> := [10, 0, 6, 2];
var seqint1 : seq<int> := [12, 2];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 6, 10, 14];
var seqint1 : seq<int> := [20, 0, 0, 0, 0, 2, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 18];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 3 - TIME: 19.3798428 s

method {:test} Test24() {
var seqint0 : seq<int> := [22, 0, 11, 0, 26, 0, 0, 4];
var seqint1 : seq<int> := [24, 0, 0, 0, 0, 4, 15, 19];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test25() {
var seqint0 : seq<int> := [26, 11, 0, 19, 28];
var seqint1 : seq<int> := [24, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 4, 30];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 4 - TIME: 20.6426597 s

method {:test} Test26() {
var seqint0 : seq<int> := [0, 0, 0, 27, 17, 23, 31];
var seqint1 : seq<int> := [27, 8];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test27() {
var seqint0 : seq<int> := [23, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 17, 35];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 37, 39];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 5 - TIME: 21.9917189 s

method {:test} Test28() {
var seqint0 : seq<int> := [42, 0, 0, 13, 25, 40];
var seqint1 : seq<int> := [44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 36, 0, 32, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 44, 0, 0, 40, 42, 0, 0, 46, 25, 13, 0, 0, 52, 0, 0, 0, 50, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 48, 0, 32, 0, 0, 0, 0, 54, 0, 0, 0, 56, 0, 58];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 23.3879666 s

method {:test} Test30() {
var seqint0 : seq<int> := [0, 0, 0, 0, 34, 41, 0, 0, 0, 0, 0, 0, 53, 0, 0, 66, 45, 49, 0, 0, 0, 57, 0, 60];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 64, 0, 66, 0, 68];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test31() {
var seqint0 : seq<int> := [60, 0, 34, 0, 49, 0, 41, 0, 53, 0];
var seqint1 : seq<int> := [57, 21, 0, 45];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 7 - TIME: 25.3260279 s

method {:test} Test32() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 43, 0, 0, 70, 0, 0, 0, 0, 0, 51, 0, 0, 0, 59, 0, 0, 29, 67, 72, 0, 0, 76];
var seqint1 : seq<int> := [80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 63, 0, 74, 0, 78, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test33() {
var seqint0 : seq<int> := [72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 51, 67, 0, 0, 0, 0, 0, 0, 63, 0, 0];
var seqint1 : seq<int> := [59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 8 - TIME: 27.2929136 s

method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 55, 0, 71];
var seqint1 : seq<int> := [79, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 0, 0, 0, 75];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test35() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 65];
var seqint1 : seq<int> := [75, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 9 - TIME: 29.3959157 s

method {:test} Test36() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 77];
var seqint1 : seq<int> := [84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}
method {:test} Test37() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 69];
var seqint1 : seq<int> := [77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 10 - TIME: 31.2799073 s
