method {:testEntry} contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{  
    var i := 0;
    var s: set<int> := {};
    while (i < |nums|)
        invariant i <= |nums|
        invariant forall j :: j in nums[..i] <==> j in s
        invariant distinct(nums[..i])
    {
        var num := nums[i];
        if (num in s)
        {
            return false;
        }

        s := s + {num};
        i := i + 1;
    }

    return true;
}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991145, -999991145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999991145, -999991145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 1 - TIME: 9.06764 s

method {:test} Test13() {
var seqint0 : seq<int> := [-999998763, 0, -999998762, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998764];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test14() {
var seqint0 : seq<int> := [-999991635, -999991145, -999991145];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 2 - TIME: 10.4247945 s

method {:test} Test15() {
var seqint0 : seq<int> := [0, 0, 0, -2, 1236, -1, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test16() {
var seqint0 : seq<int> := [-999997718, 0, 0, -999991635, 0, 0, -999998204, -999998204, 0, 0, 0, 0, -999999551, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 3 - TIME: 11.5006149 s

method {:test} Test17() {
var seqint0 : seq<int> := [1236, 0, 0, 1235, 1198, -3, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test18() {
var seqint0 : seq<int> := [-999999719, 0, 0, 0, -999997718, 0, 0, -999994147, 0, 0, -999991635, -999991635, -999991902, -999998858];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 4 - TIME: 12.8550074 s

method {:test} Test19() {
var seqint0 : seq<int> := [1831, 0, 1832, -4, 33, 1830];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test20() {
var seqint0 : seq<int> := [-999993717, 0, 0, -999999391, 0, -999994147, -999997718, -999997718];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 5 - TIME: 13.9809227 s

method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, -999996478, -999997715, 0, -999997716, 0, 0, 0, -999999067, 0, 0, 0, 0, 0, 0, 0, -999997717];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test22() {
var seqint0 : seq<int> := [-999997718, -999991145, -999991145, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 6 - TIME: 14.977937 s

method {:test} Test23() {
var seqint0 : seq<int> := [143, 5997];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test24() {
var seqint0 : seq<int> := [-999995321, 0, -999997718, -999997718, -999994147, 0, -999991902, -999998858, -999999719, 0, -999999391, 0, -999994080, 0, -999991055, 0, 0, 0, -999999465, 0, -999997003];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 7 - TIME: 16.1582895 s

method {:test} Test25() {
var seqint0 : seq<int> := [-999994142, -999994147, -999994145, -999994146, -999994144, -999994141, -999994143];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test26() {
var seqint0 : seq<int> := [-999993717, -999993717, 0, -999999551, -999994147, 0, -999991902, -999998858, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 8 - TIME: 17.4490527 s

method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999997650, 0, 0, -999997653, -999997935, -999997652, -999997651];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test28() {
var seqint0 : seq<int> := [0, 0, 0, 0, -999991635, 0, -999997718, -999999551, -999999391, -999994147, 0, 0, 0, 0, 0, 0, 0, 0, 0, -999998204, -999998204, -999999719, 0, 0, 0, 0, 0, 0, 0, -999998858];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 9 - TIME: 18.5450552 s

method {:test} Test29() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}
method {:test} Test30() {
var seqint0 : seq<int> := [0, -999998204, -999998204, 0, 0, 0, 0, 0, 0, 0, 0, -999991635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect 1 <= |seqint0| <= 100000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -1000000000 <= seqint0[i] <= 1000000000, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := contains_duplicate(seqint0);
expect r0 <==> distinct(seqint0);
}

// REPEAT 10 - TIME: 19.8605016 s
