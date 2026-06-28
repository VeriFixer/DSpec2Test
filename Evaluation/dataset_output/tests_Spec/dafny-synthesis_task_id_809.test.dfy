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
        if a[i] <= b[i]
        {
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
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -6569, 0, 0, 0, -1236];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 1796, 0, 0, 0, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 1 - TIME: 3.2990989 s

method {:test} Test2() {
var seqint0 : seq<int> := [450, 1797, 0, 8365];
var seqint1 : seq<int> := [449, 1796, 0, 8364];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test3() {
var seqint0 : seq<int> := [3, -1236];
var seqint1 : seq<int> := [5, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 2 - TIME: 4.6132322 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 1797, 8365];
var seqint1 : seq<int> := [0, 1796, 8364];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test5() {
var seqint0 : seq<int> := [-6569, 0, 0, 0, -1236];
var seqint1 : seq<int> := [1796, 0, 0, 0, 1201];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 3 - TIME: 5.8511111 s

method {:test} Test6() {
var seqint0 : seq<int> := [840, 8457, 2241];
var seqint1 : seq<int> := [839, 8456, 2240];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test7() {
var seqint0 : seq<int> := [9, -8365, 7];
var seqint1 : seq<int> := [11, 2437, 4];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 4 - TIME: 7.315507 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 9725, 0, 0, 0, 9531, 0, 0, 0, 0, 0, 0, 0, 2456, 0, 0, 0, 0, 0, 0, 0, 0, 0, 591, 0, 0, 7630, 7578, 2212];
var seqint1 : seq<int> := [0, 9724, 0, 0, 0, 3609, 0, 0, 0, 0, 0, 0, 0, 2455, 0, 0, 0, 0, 0, 0, 0, 0, 0, 590, 0, 0, 7629, 7577, 2211];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test9() {
var seqint0 : seq<int> := [15, 0, 0, 0, 0, 17, 0, 0, -6418, 0, 0, -6569];
var seqint1 : seq<int> := [0, 10, 0, 0, 13, 19, 0, 0, 2437, 0, 21, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 5 - TIME: 8.797055 s

method {:test} Test10() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 0, 0, -1236, 12, -6569];
var seqint1 : seq<int> := [20, 0, 0, 1201, 16, 1796];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 6 - TIME: 10.3562306 s

method {:test} Test12() {
var seqint0 : seq<int> := [1143, 0, 0, 0, 0, 0, 450, 0, 2282, 0, 0];
var seqint1 : seq<int> := [1142, 0, 0, 0, 0, 0, 449, 0, 2281, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, -1236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 26, 0, 7059, 0, 0, 0, 0, 30];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 22, 0, 0, 1201, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 8855, 0, 0, 0, 0, 28];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 7 - TIME: 11.8277841 s

method {:test} Test14() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5854];
var seqint1 : seq<int> := [1141, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test15() {
var seqint0 : seq<int> := [32, 0, 0, 0, 0, 0, -8365, 0, 18, -6418, 0, 29, 0];
var seqint1 : seq<int> := [34, 0, 0, 0, 0, 0, -6083, 0, 0, 2437, 0, 25, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 8 - TIME: 13.0889515 s

method {:test} Test16() {
var seqint0 : seq<int> := [8879, 0, 0, 0, 0, 0, 5921, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8945, 0, 0, 975, 1654, 0, 0];
var seqint1 : seq<int> := [8878, 0, 0, 0, 0, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8944, 0, 0, 974, 1653, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -1201, 0, 0, 7059, 0, 0, 23, 0, 0];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 1236, 31, 0, 8855, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 9 - TIME: 14.391134 s

method {:test} Test18() {
var seqint0 : seq<int> := [536, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [535, 0, 0, 0, 0, 0, 5852, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}
method {:test} Test19() {
var seqint0 : seq<int> := [41, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6418, 0, 0, 1833, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27];
var seqint1 : seq<int> := [39, 0, 0, 0, 0, 0, 35, 0, 0, 0, 2437, 0, 0, 2282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37];
expect |seqint0| == |seqint1|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := IsSmaller(seqint0, seqint1);
expect r0 <==> forall i :: 0 <= i < |seqint0| ==> seqint0[i] > seqint1[i];
expect !r0 <==> exists i :: 0 <= i < |seqint0| && seqint0[i] <= seqint1[i];
}

// REPEAT 10 - TIME: 15.8568192 s
