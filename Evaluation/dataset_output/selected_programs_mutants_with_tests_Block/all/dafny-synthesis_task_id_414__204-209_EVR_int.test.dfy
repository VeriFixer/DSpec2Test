// dafny-synthesis_task_id_414.dfy

method {:testEntry} AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |seq1| && seq1[i] in seq2
{
  result := false;
  for i := 0 to 0
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

// REPEAT 1 - TIME: 2.437217 s

method {:test} Test1() {
var seqint0 : seq<int> := [3, 1];
var seqint1 : seq<int> := [1];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 2 - TIME: 3.4133462 s

method {:test} Test2() {
var seqint0 : seq<int> := [2];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 0, 7];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 3 - TIME: 4.3661885 s

method {:test} Test3() {
var seqint0 : seq<int> := [0, 4, 8, 10];
var seqint1 : seq<int> := [12, 4];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 4 - TIME: 5.2412945 s

method {:test} Test4() {
var seqint0 : seq<int> := [16, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14];
var seqint1 : seq<int> := [18, 6, 11];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 5 - TIME: 6.0168171 s

method {:test} Test5() {
var seqint0 : seq<int> := [21, 23, 9];
var seqint1 : seq<int> := [25, 0, 0, 0, 0, 0, 9, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 19];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 6 - TIME: 7.0367774 s

method {:test} Test6() {
var seqint0 : seq<int> := [35, 20, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 13, 29];
var seqint1 : seq<int> := [33, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 27];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 7 - TIME: 8.0156958 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 26, 0, 17, 0, 0, 0, 0, 0, 30, 34, 0, 0, 0, 0, 0, 41];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 37];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 8 - TIME: 9.0412041 s

method {:test} Test8() {
var seqint0 : seq<int> := [22, 49, 0, 42, 0, 38];
var seqint1 : seq<int> := [47, 22, 32, 45];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 9 - TIME: 10.0816073 s

method {:test} Test9() {
var seqint0 : seq<int> := [46, 50, 40];
var seqint1 : seq<int> := [50, 0, 0, 28, 0];
var r0 := AnyValueExists(seqint0, seqint1);
expect r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] in seqint1;
}

// REPEAT 10 - TIME: 11.2072402 s
