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
var seqint0 : seq<int> := [-13, 3];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 1 - TIME: 2.6633498 s

method {:test} Test1() {
var seqint0 : seq<int> := [-76, -76];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [-65, 17];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 2 - TIME: 3.9919007 s

method {:test} Test3() {
var seqint0 : seq<int> := [-1, 96, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 3 - TIME: 5.2094006 s

method {:test} Test4() {
var seqint0 : seq<int> := [-20, -20, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [-52, -51, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 4 - TIME: 7.0232332 s

method {:test} Test6() {
var seqint0 : seq<int> := [-28, -22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -22];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 5 - TIME: 7.80583 s

method {:test} Test7() {
var seqint0 : seq<int> := [-87, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 6 - TIME: 8.5436752 s

method {:test} Test8() {
var seqint0 : seq<int> := [-69, 7, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 7 - TIME: 9.2332837 s

method {:test} Test9() {
var seqint0 : seq<int> := [-13, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 8 - TIME: 9.9955798 s

method {:test} Test10() {
var seqint0 : seq<int> := [-86, -71, 0, -71, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 9 - TIME: 10.5686674 s

method {:test} Test11() {
var seqint0 : seq<int> := [17, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 10 - TIME: 11.247482 s
