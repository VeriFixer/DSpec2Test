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
var seqint0 : seq<int> := [449, 7916, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2512, 0, 5853, 5853];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8365) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8365), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8365);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2282, -486, 609, 609, 1187];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 1796) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 1796), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 1796);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 5853, -2147489501, 1142, 1142, -2147484790];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, -2147483648) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, -2147483648), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, -2147483648);
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609, 2147483038, 2147475549, 2147475549, 8098];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 2147483647) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 2147483647), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 2147483647);
}
method {:test} Test4() {
var seqint0 : seq<int> := [2512, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7916, 0, 0, 0, 0, 0, 0, 0, 449, 449];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 8365) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 8365), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 8365);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 449, 160, 0, 0, 0, 0, 0, 0, 0, 5853, -5244, -5244];
expect exists i: nat, j: nat :: i < j < |seqint0| && summingPair(i, j, seqint0, 609) && forall l: nat, m: nat :: l < m < |seqint0| && l != i && m != j ==> !summingPair(l, m, seqint0, 609), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := twoSum(seqint0, 609);
}
