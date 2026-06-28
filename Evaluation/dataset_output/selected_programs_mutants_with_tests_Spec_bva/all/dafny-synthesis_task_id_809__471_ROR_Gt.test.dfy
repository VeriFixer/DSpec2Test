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
    if a[i] > b[i] {
      result := false;
      break;
    }
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -6569, 0, 0, 0, -1236];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 1796, 0, 0, 0, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test12() {
var seqint0 : seq<int> := [-1239];
var seqint1 : seq<int> := [1198];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test13() {
var seqint0 : seq<int> := [6483, -8855];
var seqint1 : seq<int> := [7719, -7059];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test14() {
var seqint0 : seq<int> := [-8882];
var seqint1 : seq<int> := [-6445];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -1796, 0, 0, 0, -1236];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 6569, 0, 0, 0, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -1796, 0, 0, 0, -1201];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 6569, 0, 0, 0, 1236];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 1 - TIME: 15.2639385 s

method {:test} Test20() {
var seqint0 : seq<int> := [0, 2437, 0];
var seqint1 : seq<int> := [0, 2436, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, -1201, 0, 3];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 5];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 2 - TIME: 16.809728 s

method {:test} Test22() {
var seqint0 : seq<int> := [8221, 1888, 0, 0, 1324, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5905];
var seqint1 : seq<int> := [8220, 1887, 0, 0, 1323, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5904];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test23() {
var seqint0 : seq<int> := [0, 0, 0, -1236, 0, 0, 0, 0, 7059, 0, 9, 0];
var seqint1 : seq<int> := [0, 0, 0, 1201, 0, 0, 0, 7, 8855, 0, 11, 13];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 3 - TIME: 18.3310899 s

method {:test} Test24() {
var seqint0 : seq<int> := [591, 0, 0, 0, 0, 0, 0, 4679, 0, 0, 2241, 0, 2276, 0, 0, 6284, 0, 0, 0, 0, 0, 5904, 0, 1324];
var seqint1 : seq<int> := [590, 0, 0, 0, 0, 0, 0, 4678, 0, 0, 2240, 0, 2275, 0, 0, 6283, 0, 0, 0, 0, 0, 5903, 0, 1323];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test25() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, -8365, 0, 0, 12, 0, 0, 17, 0, 0, -2437, 0];
var seqint1 : seq<int> := [0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6083, 0, 0, 15, 0, 0, 0, 0, 19, 6418, 23];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 4 - TIME: 19.9395811 s

method {:test} Test26() {
var seqint0 : seq<int> := [3153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7854, 0, 6927, 0, 0, 2332, 0, 4771, 0, 2113, 1650, 6703];
var seqint1 : seq<int> := [3152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7853, 0, 6926, 0, 0, 2331, 0, 4770, 0, 2112, 1649, 6702];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -6569, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, -1201, 0, 0, 0, 20, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 0, 0, 0, 16];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 5 - TIME: 21.6196714 s

method {:test} Test28() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 281, 0, 610, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 280, 0, 609, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8365, 0, 0, 0, -1201, 0, 0, 0, 22];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6083, 0, 0, 0, 1236, 0, 14, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 6 - TIME: 23.2547071 s

method {:test} Test30() {
var seqint0 : seq<int> := [536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8945, 0, 0, 0, 5853, 1142];
var seqint1 : seq<int> := [535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8944, 0, 0, 0, 5852, 1141];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test31() {
var seqint0 : seq<int> := [27, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6569, 0, 0, 25];
var seqint1 : seq<int> := [29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 0, 18];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 7 - TIME: 24.9084063 s

method {:test} Test32() {
var seqint0 : seq<int> := [7719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [7718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test33() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2437, 0, 0, 0, 0, 0, 1833, 0, 0, 0, 0];
var seqint1 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6418, 0, 0, 0, 0, 0, 2282, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 8 - TIME: 27.0272281 s

method {:test} Test34() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test35() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2282, 0, 0, -2437, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1833, 0, 0, 6418, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 9 - TIME: 29.3815563 s

method {:test} Test36() {
var seqint0 : seq<int> := [7720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [7719, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test37() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -8365, 0, 0, -6418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, -6083, 0, 0, 2437, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 10 - TIME: 31.6694255 s
