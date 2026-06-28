// dafny-synthesis_task_id_399.dfy

method {:testEntry} BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] ^ b[k]
  {
    result := [a[i] ^ b[i]];
    i := 1;
  }
}


method {:test} Test0() {
var seqbv0 : seq<bv32> := [4294967295];
var seqbv1 : seq<bv32> := [0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 1 - TIME: 2.4781816 s

method {:test} Test1() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 3];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 2 - TIME: 3.414434 s

method {:test} Test2() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32), 10, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 4, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 6];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 3 - TIME: 4.2823162 s

method {:test} Test3() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), 0];
var seqbv1 : seq<bv32> := [0, 2, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 4 - TIME: 5.3587337 s

method {:test} Test4() {
var seqbv0 : seq<bv32> := [4294967295, 2147483648, 0, (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 0, 0, (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 5 - TIME: 6.405717 s

method {:test} Test5() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 6 - TIME: 7.364581 s

method {:test} Test6() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), 7, (0 as bv32), (0 as bv32), 0];
var seqbv1 : seq<bv32> := [0, 1, (0 as bv32), (0 as bv32), 9, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 7 - TIME: 8.1614603 s

method {:test} Test7() {
var seqbv0 : seq<bv32> := [4294967295, 17, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 21, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 25, 11, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), 15, 19, (0 as bv32), (0 as bv32), (0 as bv32), 13, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 5, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 23];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 8 - TIME: 8.917056 s

method {:test} Test8() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 9 - TIME: 9.8547177 s

method {:test} Test9() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 10 - TIME: 10.9016233 s
