method {:testEntry} remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{
        var previous := nums[0];
        result := [nums[0]];

        var i := 1;
        while (i < |nums|)
            invariant 0 <= i <= |nums|
            invariant |result| >= 1;
            invariant previous in nums[0..i];   
            invariant previous == result[|result| - 1];
            invariant is_sorted_and_distinct(result)
            invariant forall j :: j in nums[0..i] <==> j in result
        {
            if (previous != nums[i])
            { 
                result := result + [nums[i]];
                previous := nums[i];
            }

            i := i + 1;
        }
}


// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}

method {:test} Test0() {
var seqint0 : seq<int> := [-20, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 1 - TIME: 9.3504205 s

method {:test} Test1() {
var seqint0 : seq<int> := [37, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 2 - TIME: 15.7563731 s

method {:test} Test2() {
var seqint0 : seq<int> := [-65, 0, 0, 0, 0, 0, 0, 0, -65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 3 - TIME: 21.7082301 s

method {:test} Test3() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 4 - TIME: 27.8487877 s

method {:test} Test4() {
var seqint0 : seq<int> := [-55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -55];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 5 - TIME: 34.3090071 s

method {:test} Test5() {
var seqint0 : seq<int> := [61, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 6 - TIME: 41.277195 s

method {:test} Test6() {
var seqint0 : seq<int> := [24, 0, 0, 24, 24];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 7 - TIME: 48.8410005 s

method {:test} Test7() {
var seqint0 : seq<int> := [-76, 0, 0, -76];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 8 - TIME: 57.3301067 s

method {:test} Test8() {
var seqint0 : seq<int> := [-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 9 - TIME: 64.2799906 s

method {:test} Test9() {
var seqint0 : seq<int> := [99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 10 - TIME: 70.9416208 s
