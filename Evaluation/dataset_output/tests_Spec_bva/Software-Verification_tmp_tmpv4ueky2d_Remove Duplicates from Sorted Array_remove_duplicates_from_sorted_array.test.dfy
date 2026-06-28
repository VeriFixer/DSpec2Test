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
var seqint0 : seq<int> := [0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 1 - TIME: 16.1254546 s

method {:test} Test9() {
var seqint0 : seq<int> := [33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 2 - TIME: 17.6664629 s

method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, -19];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 3 - TIME: 19.2328878 s

method {:test} Test11() {
var seqint0 : seq<int> := [-55, 3];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 4 - TIME: 20.7101075 s

method {:test} Test12() {
var seqint0 : seq<int> := [0, 33, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 5 - TIME: 22.2573458 s

method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 33, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 6 - TIME: 24.0156038 s

method {:test} Test14() {
var seqint0 : seq<int> := [33, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 7 - TIME: 25.566672 s

method {:test} Test15() {
var seqint0 : seq<int> := [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 8 - TIME: 26.9221948 s

method {:test} Test16() {
var seqint0 : seq<int> := [0, 0, -72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 9 - TIME: 28.323766 s

method {:test} Test17() {
var seqint0 : seq<int> := [-75, 0, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 10 - TIME: 29.884856 s
