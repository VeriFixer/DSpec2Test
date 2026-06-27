// dafny-synthesis_task_id_809.dfy

method {:testEntry} IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  requires |a| == |b|
  ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
  ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
{
  result := true;
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant result <==> forall k :: 0 <= k < i ==> a[k] > b[k]
    invariant !result <==> exists k :: 0 <= k < i && a[k] <= b[k]
  {
    break;
    if a[i] <= b[i] {
      result := false;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 6483];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 7719];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 1 - TIME: 3.0231656 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, -6418, 0, 610, 0, 0, 0, 0, 0, 0, 2283];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 2437, 0, 609, 0, 0, 0, 0, 0, 0, 2282];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 2 - TIME: 3.9551267 s

method {:test} Test2() {
var seqint0 : seq<int> := [8945, 0, 0, 0, 0, -5244, 0, 0, 0, 8099];
var seqint1 : seq<int> := [8944, 0, 0, 0, 0, 609, 0, 0, 0, 8098];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 3 - TIME: 5.0398696 s

method {:test} Test3() {
var seqint0 : seq<int> := [5853, 0, 0, 0, 0, 7059, 0, 0, 0, 0, 449];
var seqint1 : seq<int> := [5852, 0, 0, 0, 0, 8855, 0, 0, 0, 0, 448];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 4 - TIME: 6.1248718 s

method {:test} Test4() {
var seqint0 : seq<int> := [256, 536, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0];
var seqint1 : seq<int> := [9111, 535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 5 - TIME: 7.2550369 s

method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8879, 2446, 0, 0, 0, 4680, 840, -2245, 6907];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1653, 2445, 0, 0, 0, 4679, 839, 5853, 6906];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 6 - TIME: 8.4622052 s

method {:test} Test6() {
var seqint0 : seq<int> := [2283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1797, 0, 0, 0, 0, -6418];
var seqint1 : seq<int> := [2282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 2437];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 7 - TIME: 9.671303 s

method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, -1201, 0, 0, 0, 0, 0, 0, 0, 0, 2283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 609];
var seqint1 : seq<int> := [0, 0, 1236, 0, 0, 0, 0, 0, 0, 0, 0, 2282, 9, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 608];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 8 - TIME: 10.636884 s

method {:test} Test8() {
var seqint0 : seq<int> := [8945, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6956, 282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [8944, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8098, 281, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 9 - TIME: 11.7088304 s

method {:test} Test9() {
var seqint0 : seq<int> := [2438, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6483];
var seqint1 : seq<int> := [2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7719];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 10 - TIME: 12.8784334 s
