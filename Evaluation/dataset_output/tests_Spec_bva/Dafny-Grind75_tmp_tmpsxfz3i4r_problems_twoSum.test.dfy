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
method {:test} Test1() {
var seqint0 : seq<int> := [0, 449, 7916, 0, 0, 0, 0, 0, 0, 2512, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 5853];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8365) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8365), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8365);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 8098, -8198, 0, 0, 0, 0, 0, -381, 0, 0, 0, 0, 0, 281, 281];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, -100) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, -100), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, -100);
}
method {:test} Test3() {
var seqint0 : seq<int> := [609, -509, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8098, 0, 0, 0, 0, 0, 0, -7998, -7998];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 100) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 100), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 100);
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 1187, 609, 0, 0, 0, 0, 0, 2282, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2282, -486];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 1796) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 1796), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 1796);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 2282, -486, 609, 609, 1187];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 1796) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 1796), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 1796);
}

// REPEAT 1 - TIME: 142.671456 s

method {:test} Test7() {
var seqint0 : seq<int> := [8852, 1796, 2283, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 10, 0, 2283, 8365];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 10648) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 10648), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 10648);
}

// REPEAT 2 - TIME: 156.4880975 s

method {:test} Test8() {
var seqint0 : seq<int> := [5, 0, 0, 18138, 18138, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 12894, 5853];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 18747) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 18747), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 18747);
}

// REPEAT 3 - TIME: 170.7346932 s

method {:test} Test9() {
var seqint0 : seq<int> := [8855, 11689, 12179, 12179, 8365];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 20544) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 20544), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 20544);
}

// REPEAT 4 - TIME: 184.8553905 s

method {:test} Test10() {
var seqint0 : seq<int> := [449, 25949, 609, 0, 0, 0, 0, 0, 0, 0, 25789, 25789, 0, 0, 0, 0, 9, 12];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 26398) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 26398), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 26398);
}

// REPEAT 5 - TIME: 199.8389058 s

method {:test} Test11() {
var seqint0 : seq<int> := [13, 0, 18483, 8365, 26239, 26239, 609, 0, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 26848) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 26848), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 26848);
}

// REPEAT 6 - TIME: 213.7697638 s

method {:test} Test12() {
var seqint0 : seq<int> := [32093, 609, 0, 0, 0, 0, 0, 0, 0, 32253, 0, 0, 0, 11, 0, 32253, 449, 15];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 32702) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 32702), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 32702);
}

// REPEAT 7 - TIME: 227.3030292 s

method {:test} Test13() {
var seqint0 : seq<int> := [27459, 27459, 0, 0, 5853, 5853];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 33312) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 33312), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 33312);
}

// REPEAT 8 - TIME: 240.2785229 s

method {:test} Test14() {
var seqint0 : seq<int> := [38557, 38557, 609, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 18, 0, 0, 20, 0, 0, 22, 24, 449, 38717, 0, 28, 0];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 39166) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 39166), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 39166);
}

// REPEAT 9 - TIME: 253.1433387 s

method {:test} Test15() {
var seqint0 : seq<int> := [32598, 8365, 32598, 8365];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 40963) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 40963), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 40963);
}

// REPEAT 10 - TIME: 266.9225342 s
