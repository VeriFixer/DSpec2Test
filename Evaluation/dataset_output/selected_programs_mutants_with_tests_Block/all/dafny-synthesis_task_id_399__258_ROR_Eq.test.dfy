// dafny-synthesis_task_id_399.dfy

method {:testEntry} BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{
  result := [];
  var i := 0;
  while i == |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] ^ b[k]
  {
    result := result + [a[i] ^ b[i]];
    i := i + 1;
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

// REPEAT 1 - TIME: 2.3591838 s

method {:test} Test1() {
var seqbv0 : seq<bv32> := [4294967295, 0];
var seqbv1 : seq<bv32> := [0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 2 - TIME: 3.1345801 s

method {:test} Test2() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 3 - TIME: 3.9075176 s

method {:test} Test3() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 4 - TIME: 4.6790777 s

method {:test} Test4() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), 0, 3, (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 5, 0, (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 5 - TIME: 5.5359004 s

method {:test} Test5() {
var seqbv0 : seq<bv32> := [4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 6 - TIME: 6.4544023 s

method {:test} Test6() {
var seqbv0 : seq<bv32> := [4294967295, 2147483648, 0];
var seqbv1 : seq<bv32> := [0, 2147483648, 2147483648];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 7 - TIME: 7.4830382 s

method {:test} Test7() {
var seqbv0 : seq<bv32> := [4294967295, 6, 2147483648, 0, (0 as bv32), 0];
var seqbv1 : seq<bv32> := [0, (0 as bv32), 2147483648, 0, 1, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 8 - TIME: 8.6069655 s

method {:test} Test8() {
var seqbv0 : seq<bv32> := [4294967295, 2147483648, (0 as bv32), 0, 0];
var seqbv1 : seq<bv32> := [0, 2147483648, (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 9 - TIME: 9.7326112 s

method {:test} Test9() {
var seqbv0 : seq<bv32> := [4294967295, 2147483648, 0, (0 as bv32), 2, (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 2147483648, 0, (0 as bv32), (0 as bv32), 8, 10];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 10 - TIME: 10.6295398 s
