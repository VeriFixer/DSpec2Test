/*
https://leetcode.com/problems/two-sum/
function twoSum(nums: number[], target: number): number[] {
    const n = nums.length;
    for(let i = 0; i < n; i++) {
        for(let k = i+1; k < n; k++) {
            if(nums[i] + nums[k] == target) return [i,k]; 
        }
    }
};
*/
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
method {:testEntry} twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    pair := (0,0);
    var i: nat := 0;
    while i < |nums| 
        invariant i <= |nums|
        invariant forall z: nat, j: nat :: 0 <= z < i  && z+1 <= j < |nums| ==> !summingPair(z, j, nums, target)
    {
        var k: nat := i + 1;
        while k < |nums| 
            invariant i + 1 <= k <= |nums|
            // invariant forall q: nat :: i+1 <= q < k < |nums| ==> !summingPair(i,q, nums, target) //this fails to verify
            invariant forall q: nat :: i+1 <= q < k <= |nums| ==> !summingPair(i,q, nums, target) //this verifies
        {
            // assert i < k < |nums|;
            if nums[i] + nums[k] == target {
                pair := (i,k);
                return pair;
            }
            k := k + 1;
        }
        i := i + 1;
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 2282, -486, 0, 0, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609, 1187];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 1796) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 1796), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 1796);
}

// REPEAT 1 - TIME: 14.9605675 s

method {:test} Test1() {
var seqint0 : seq<int> := [3630, 0, 0, 0, 0, 0, 5853, -1774, 0, 3630, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 449];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 4079) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 4079), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 4079);
}

// REPEAT 2 - TIME: 26.0029671 s

method {:test} Test2() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9324, 609, 2282, 7651, 7651];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 9933) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 9933), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 9933);
}

// REPEAT 3 - TIME: 36.7875774 s

method {:test} Test3() {
var seqint0 : seq<int> := [8, 0, 12179, 12179, 0, 5853, 0, 0, 0, 0, 0, 0, 609, 17423, 0, 6];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 18032) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 18032), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 18032);
}

// REPEAT 4 - TIME: 47.0772605 s

method {:test} Test4() {
var seqint0 : seq<int> := [23277, 449, 23437, 23277, 0, 0, 0, 0, 609];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 23886) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 23886), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 23886);
}

// REPEAT 5 - TIME: 57.0103612 s

method {:test} Test5() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29131, 609, 2282, 27458, 27458, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 29740) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 29740), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 29740);
}

// REPEAT 6 - TIME: 66.8820731 s

method {:test} Test6() {
var seqint0 : seq<int> := [17, 0, 449, 31574, 0, 0, 0, 0, 0, 9, 0, 0, 31574, 5853, 26170, 11, 15];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 32023) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 32023), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 32023);
}

// REPEAT 7 - TIME: 76.9215585 s

method {:test} Test7() {
var seqint0 : seq<int> := [21, 0, 0, 0, 0, 0, 2282, 30351, 32184, 32184, 449, 0, 0, 0, 0, 0, 16, 0, 0, 0, 13, 0, 0, 0, 10, 0, 0, 0, 0, 19];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 32633) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 32633), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 32633);
}

// REPEAT 8 - TIME: 87.0486712 s

method {:test} Test8() {
var seqint0 : seq<int> := [22, 2282, 36205, 0, 0, 0, 0, 0, 0, 609, 0, 18, 0, 0, 0, 0, 37878, 37878];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 38487) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 38487), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 38487);
}

// REPEAT 9 - TIME: 96.9538975 s

method {:test} Test9() {
var seqint0 : seq<int> := [24, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 43732, 43732, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 609, 0, 42059, 2282, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 44341) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 44341), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 44341);
}

// REPEAT 10 - TIME: 107.1566775 s
