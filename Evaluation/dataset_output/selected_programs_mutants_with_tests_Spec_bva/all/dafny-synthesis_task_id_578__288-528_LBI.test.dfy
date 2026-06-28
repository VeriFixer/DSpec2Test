// dafny-synthesis_task_id_578.dfy

method {:testEntry} Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  requires |s1| == |s2| && |s2| == |s3|
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3 * i] == s1[i] && r[3 * i + 1] == s2[i] && r[3 * i + 2] == s3[i]
{
  r := [];
  for i := 0 to |s1|
    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k :: 0 <= k < i ==> r[3 * k] == s1[k] && r[3 * k + 1] == s2[k] && r[3 * k + 2] == s3[k]
  {
    break;
    r := r + [s1[i], s2[i], s3[i]];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
var seqint2 : seq<int> := [0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 1 - TIME: 10.5858823 s

method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 44];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 47];
var seqint2 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 43];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 2 - TIME: 11.56583 s

method {:test} Test14() {
var seqint0 : seq<int> := [60, 56, 41];
var seqint1 : seq<int> := [59, 55, 42];
var seqint2 : seq<int> := [61, 54, 40];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 3 - TIME: 12.4547619 s

method {:test} Test15() {
var seqint0 : seq<int> := [86, 62, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [87, 64, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint2 : seq<int> := [85, 63, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 4 - TIME: 13.3805092 s

method {:test} Test16() {
var seqint0 : seq<int> := [121, 0, 97, 117, 0, 0, 107, 0];
var seqint1 : seq<int> := [122, 0, 99, 110, 0, 0, 108, 0];
var seqint2 : seq<int> := [123, 0, 100, 111, 0, 0, 109, 0];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 5 - TIME: 14.513473 s

method {:test} Test17() {
var seqint0 : seq<int> := [167, 164];
var seqint1 : seq<int> := [168, 165];
var seqint2 : seq<int> := [147, 124];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 6 - TIME: 15.7445598 s

method {:test} Test18() {
var seqint0 : seq<int> := [152, 0, 0, 138, 148, 0, 127];
var seqint1 : seq<int> := [153, 0, 0, 139, 136, 0, 129];
var seqint2 : seq<int> := [154, 0, 0, 140, 137, 0, 130];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 7 - TIME: 16.7894777 s

method {:test} Test19() {
var seqint0 : seq<int> := [202, 0, 182, 0, 0, 0, 170, 189, 192];
var seqint1 : seq<int> := [203, 0, 183, 0, 0, 0, 171, 190, 193];
var seqint2 : seq<int> := [204, 0, 184, 0, 0, 0, 172, 191, 194];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 8 - TIME: 17.818067 s

method {:test} Test20() {
var seqint0 : seq<int> := [218, 0, 0, 0, 200, 213];
var seqint1 : seq<int> := [217, 0, 0, 0, 198, 212];
var seqint2 : seq<int> := [219, 0, 0, 0, 201, 214];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 9 - TIME: 19.023926 s

method {:test} Test21() {
var seqint0 : seq<int> := [258, 0, 239, 0, 243];
var seqint1 : seq<int> := [257, 0, 227, 0, 233];
var seqint2 : seq<int> := [256, 0, 229, 0, 244];
expect |seqint0| == |seqint1| && |seqint1| == |seqint2|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Interleave(seqint0, seqint1, seqint2);
expect |r0| == 3 * |seqint0|;
expect forall i :: 0 <= i < |seqint0| ==> r0[3 * i] == seqint0[i] && r0[3 * i + 1] == seqint1[i] && r0[3 * i + 2] == seqint2[i];
}

// REPEAT 10 - TIME: 20.1681835 s
