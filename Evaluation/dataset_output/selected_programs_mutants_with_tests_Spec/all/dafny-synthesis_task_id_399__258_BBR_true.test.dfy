// dafny-synthesis_task_id_399.dfy

method {:testEntry} BitwiseXOR(a: seq<bv32>, b: seq<bv32>) returns (result: seq<bv32>)
  requires |a| == |b|
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] ^ b[i]
{
  result := [];
  var i := 0;
  while true
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] ^ b[k]
  {
    result := result + [a[i] ^ b[i]];
    i := i + 1;
  }
}


method {:test} Test0() {
var seqbv0 : seq<bv32> := [(0 as bv32)];
var seqbv1 : seq<bv32> := [(0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 1 - TIME: 2.8558834 s

method {:test} Test1() {
var seqbv0 : seq<bv32> := [(0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [(0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 2 - TIME: 3.9218079 s

method {:test} Test2() {
var seqbv0 : seq<bv32> := [(0 as bv32), 4294967295, 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [(0 as bv32), 0, 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 3 - TIME: 5.0371014 s

method {:test} Test3() {
var seqbv0 : seq<bv32> := [2147483647, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [2147483648, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 4 - TIME: 6.0078424 s

method {:test} Test4() {
var seqbv0 : seq<bv32> := [2147483647, 4294967295, 4294967295, 4294967295, (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [2147483648, 0, 0, 0, (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 5 - TIME: 7.135184 s

method {:test} Test5() {
var seqbv0 : seq<bv32> := [3221225471, 2147483647, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [1073741824, 2147483648, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 6 - TIME: 8.0200658 s

method {:test} Test6() {
var seqbv0 : seq<bv32> := [4294967295, 2147483647, 4294967295, (0 as bv32), (0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [0, 2147483648, 0, (0 as bv32), (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 7 - TIME: 8.9705137 s

method {:test} Test7() {
var seqbv0 : seq<bv32> := [(0 as bv32), 4294967295, 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [(0 as bv32), 0, 0, (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 8 - TIME: 9.7815207 s

method {:test} Test8() {
var seqbv0 : seq<bv32> := [3221225471, 4294967295, (0 as bv32), 4294967295, 4294967295, (0 as bv32), 4294967295, 4294967295, (0 as bv32), (0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [1073741824, 0, (0 as bv32), 0, 0, (0 as bv32), 0, 0, (0 as bv32), (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 9 - TIME: 10.7878179 s

method {:test} Test9() {
var seqbv0 : seq<bv32> := [2147483648, 2147483647, (0 as bv32), (0 as bv32), 4294967295, (0 as bv32)];
var seqbv1 : seq<bv32> := [3221225472, 2147483648, (0 as bv32), (0 as bv32), 0, (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 10 - TIME: 11.8375718 s
