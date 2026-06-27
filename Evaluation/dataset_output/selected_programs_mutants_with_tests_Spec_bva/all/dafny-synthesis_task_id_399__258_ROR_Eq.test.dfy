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
var seqbv0 : seq<bv32> := [(0 as bv32)];
var seqbv1 : seq<bv32> := [(0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}
method {:test} Test1() {
var seqbv0 : seq<bv32> := [];
var seqbv1 : seq<bv32> := [];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}
method {:test} Test3() {
var seqbv0 : seq<bv32> := [(0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [(0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 1 - TIME: 8.7080121 s

method {:test} Test13() {
var seqbv0 : seq<bv32> := [(0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [(0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 2 - TIME: 9.4323803 s

method {:test} Test14() {
var seqbv0 : seq<bv32> := [2147483647, (0 as bv32)];
var seqbv1 : seq<bv32> := [2147483648, (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 3 - TIME: 10.2058974 s

method {:test} Test15() {
var seqbv0 : seq<bv32> := [4294967295, 2147483647, 4294967295, 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [0, 2147483648, 0, 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 4 - TIME: 10.9397881 s

method {:test} Test16() {
var seqbv0 : seq<bv32> := [2147483647, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, 4294967295];
var seqbv1 : seq<bv32> := [2147483648, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 5 - TIME: 11.605004 s

method {:test} Test17() {
var seqbv0 : seq<bv32> := [2147483647, 4294967295, (0 as bv32), 4294967295, 4294967295, (0 as bv32), 4294967295, 4294967295, (0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [2147483648, 0, (0 as bv32), 0, 0, (0 as bv32), 0, 0, (0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 6 - TIME: 12.5013016 s

method {:test} Test18() {
var seqbv0 : seq<bv32> := [4294967295, 2147483647, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, 4294967295, (0 as bv32)];
var seqbv1 : seq<bv32> := [0, 2147483648, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), 0, 0, (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 7 - TIME: 13.463695 s

method {:test} Test19() {
var seqbv0 : seq<bv32> := [2147483648, 4294967295, (0 as bv32)];
var seqbv1 : seq<bv32> := [3221225472, 0, (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 8 - TIME: 14.4770102 s

method {:test} Test20() {
var seqbv0 : seq<bv32> := [1073741824, 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 4294967295, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
var seqbv1 : seq<bv32> := [1073741824, 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), 0, (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32), (0 as bv32)];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 9 - TIME: 15.3447271 s

method {:test} Test21() {
var seqbv0 : seq<bv32> := [3221225471, 4294967295, 4294967295, (0 as bv32), 4294967295];
var seqbv1 : seq<bv32> := [1073741824, 0, 0, (0 as bv32), 0];
expect |seqbv0| == |seqbv1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := BitwiseXOR(seqbv0, seqbv1);
expect |r0| == |seqbv0|;
expect forall i :: 0 <= i < |r0| ==> r0[i] == seqbv0[i] ^ seqbv1[i];
}

// REPEAT 10 - TIME: 16.5484778 s
