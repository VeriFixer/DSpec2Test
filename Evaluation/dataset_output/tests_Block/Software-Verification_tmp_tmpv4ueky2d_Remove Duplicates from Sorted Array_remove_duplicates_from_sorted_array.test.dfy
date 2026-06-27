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

// REPEAT 1 - TIME: 2.8854351 s

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

// REPEAT 2 - TIME: 4.3100008 s

method {:test} Test3() {
var seqint0 : seq<int> := [-88, -87, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 3 - TIME: 5.3313927 s

method {:test} Test4() {
var seqint0 : seq<int> := [61, 62, 0, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 4 - TIME: 6.4005536 s

method {:test} Test5() {
var seqint0 : seq<int> := [65, 81, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 5 - TIME: 7.4706787 s

method {:test} Test6() {
var seqint0 : seq<int> := [-77, -77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}
method {:test} Test7() {
var seqint0 : seq<int> := [-60, -59, 0];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 6 - TIME: 8.8011406 s

method {:test} Test8() {
var seqint0 : seq<int> := [66, 67];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 7 - TIME: 9.5797066 s

method {:test} Test9() {
var seqint0 : seq<int> := [-35, -22, 0, 0, 55];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 8 - TIME: 10.2510547 s

method {:test} Test10() {
var seqint0 : seq<int> := [-48, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 9 - TIME: 10.9092438 s

method {:test} Test11() {
var seqint0 : seq<int> := [-100, -93, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -82];
expect is_sorted(seqint0), "If this check fails at runtime, the test does not meet the preconditions";
expect 1 <= |seqint0| <= 30000, "If this check fails at runtime, the test does not meet the preconditions";
expect forall i :: 0 <= i < |seqint0| ==> -100 <= seqint0[i] <= 100, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := remove_duplicates_from_sorted_array(seqint0);
expect is_sorted_and_distinct(r0);
expect forall i :: i in seqint0 <==> i in r0;
}

// REPEAT 10 - TIME: 11.615886 s
