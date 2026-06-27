method {:testEntry} Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	assert HasAddends(q,10) by { assert q[2]+q[4] == 4+6 == 10; }
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
	assert i == 2 && j == 4;
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method {:testEntry} FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	var sum := q[i] + q[j];

	while sum != x
		invariant LoopInv(q, x, i, j, sum)
		decreases j - i
	{
		if (sum > x)
		{
			// Sum it too big, lower it by decreasing the high index
			LoopInvWhenSumIsBigger(q, x, i, j, sum);
			j := j - 1;
		}
		// 'sum == x' cannot occur because the loop's guard is 'sum !=x'.
		else // (sum < x)
		{
			// Sum is too small, make it bigger by increasing the low index.
			i := i + 1;
		}

		sum := q[i] + q[j];
	}
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	HasAddends(q[i..(j + 1)], x)
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x;
	requires LoopInv(q, x, i, j, sum)
	ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
	assert q[i..j] < q[i..(j + 1)];
}

method {:test} Test0() {
Main();
}
method {:test} Test1() {
var seqint0 : seq<int> := [6906, 6906, 6906, 0, 0, 6906, 0, 0, 6906, 15493, 0, 15493, 15493, 15493, 16636, 0, 0, 0, 0, 0, 16636];
expect Sorted(seqint0) && HasAddends(seqint0, 22399), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 22399);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 22399;
}
method {:test} Test2() {
var seqint0 : seq<int> := [9244, 0, 0, 9244, 9245, 11706, 13981, 0, 13981, 0, 0, 0, 0, 0, 0, 0, 0, 13985, 16256, 18718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18718];
expect Sorted(seqint0) && HasAddends(seqint0, 27962), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 27962);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 27962;
}

// REPEAT 1 - TIME: 5.3735549 s

method {:test} Test3() {
var seqint0 : seq<int> := [22385, 22386, 22386, 22386, 22386, 22386, 22386, 29966, 29966, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29966];
expect Sorted(seqint0) && HasAddends(seqint0, 44772), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 44772);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 44772;
}
method {:test} Test4() {
var seqint0 : seq<int> := [13980, 13982, 13982, 13982, 13982, 13983];
expect Sorted(seqint0) && HasAddends(seqint0, 27964), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 27964);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 27964;
}

// REPEAT 2 - TIME: 7.4881073 s

method {:test} Test5() {
var seqint0 : seq<int> := [31789, 31789, 31789, 31789, 31789, 31789, 31789, 31789, 31789, 31790, 31790, 31790, 0, 0, 0, 0, 31790];
expect Sorted(seqint0) && HasAddends(seqint0, 63578), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 63578);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 63578;
}
method {:test} Test6() {
var seqint0 : seq<int> := [25881, 25888, 25889, 25889, 25889, 25889, 0, 0, 0, 25889, 25889, 25889, 0, 0, 0, 25896, 0, 48283];
expect Sorted(seqint0) && HasAddends(seqint0, 51778), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 51778);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 51778;
}

// REPEAT 3 - TIME: 9.7753154 s

method {:test} Test7() {
var seqint0 : seq<int> := [35424, 35424, 35424, 35424, 35424, 0, 0, 0, 0, 0, 0, 0, 0, 35424, 35424, 35424, 35424, 35424, 35425, 35425];
expect Sorted(seqint0) && HasAddends(seqint0, 70848), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 70848);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 70848;
}
method {:test} Test8() {
var seqint0 : seq<int> := [29610, 38123, 38123, 38123, 38123, 40666, 46635];
expect Sorted(seqint0) && HasAddends(seqint0, 76246), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 76246);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 76246;
}

// REPEAT 4 - TIME: 11.7831256 s

method {:test} Test9() {
var seqint0 : seq<int> := [40233, 40234, 0, 40234, 40234, 40235, 40236, 40236, 40236, 40236, 40236, 40236, 40237, 40237, 40237, 40237, 0, 0, 0, 0, 41107, 41107, 48993];
expect Sorted(seqint0) && HasAddends(seqint0, 80472), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 80472);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 80472;
}
method {:test} Test10() {
var seqint0 : seq<int> := [44505, 44507, 44509, 44511, 44513, 44514, 0, 0, 0, 0, 0, 44515, 44517, 44518, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44519];
expect Sorted(seqint0) && HasAddends(seqint0, 89024), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 89024);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 89024;
}

// REPEAT 5 - TIME: 14.3017026 s

method {:test} Test11() {
var seqint0 : seq<int> := [54155, 54155, 54155, 54155, 54155, 54155, 54155, 54155, 54156, 54157, 54157, 54157, 54157, 54157, 54157];
expect Sorted(seqint0) && HasAddends(seqint0, 108310), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 108310);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 108310;
}
method {:test} Test12() {
var seqint0 : seq<int> := [39206, 47211, 47212, 47212, 47213, 47214, 47214];
expect Sorted(seqint0) && HasAddends(seqint0, 94424), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 94424);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 94424;
}

// REPEAT 6 - TIME: 16.384818 s

method {:test} Test13() {
var seqint0 : seq<int> := [56934, 56934, 62678, 62678, 62678, 62678, 62678, 62678, 0, 0, 62678, 62678, 68423, 0, 0, 0, 68423];
expect Sorted(seqint0) && HasAddends(seqint0, 125356), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 125356);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 125356;
}
method {:test} Test14() {
var seqint0 : seq<int> := [55211, 0, 0, 0, 55218, 55218, 55218, 55218, 55218, 55218, 55218, 55223, 55224, 109380];
expect Sorted(seqint0) && HasAddends(seqint0, 110436), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 110436);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 110436;
}

// REPEAT 7 - TIME: 18.4470482 s

method {:test} Test15() {
var seqint0 : seq<int> := [63425, 0, 63425, 63425, 63425, 63425, 63425, 63425, 63425, 63425, 63426, 0, 63426];
expect Sorted(seqint0) && HasAddends(seqint0, 126850), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 126850);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 126850;
}
method {:test} Test16() {
var seqint0 : seq<int> := [71264, 71265, 71265, 71265, 0, 0, 0, 71265, 71265, 71265, 71265, 71265, 71265, 71265, 71265, 71265];
expect Sorted(seqint0) && HasAddends(seqint0, 142530), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 142530);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 142530;
}

// REPEAT 8 - TIME: 20.5374373 s

method {:test} Test17() {
var seqint0 : seq<int> := [73882, 73882, 73882, 73882, 73882, 73882, 73882, 73882, 0, 0, 73882, 73882, 73883, 73883];
expect Sorted(seqint0) && HasAddends(seqint0, 147764), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 147764);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 147764;
}
method {:test} Test18() {
var seqint0 : seq<int> := [74034, 74036, 74036, 74038, 74038, 74038, 74038, 74039, 74039, 74040, 0, 74041, 0, 74041];
expect Sorted(seqint0) && HasAddends(seqint0, 148076), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 148076);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 148076;
}

// REPEAT 9 - TIME: 23.1098575 s

method {:test} Test19() {
var seqint0 : seq<int> := [75857, 75857, 75857, 75857, 0, 75857, 75857, 0, 0, 0, 0, 75857, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75857, 75858];
expect Sorted(seqint0) && HasAddends(seqint0, 151714), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 151714);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 151714;
}
method {:test} Test20() {
var seqint0 : seq<int> := [79093, 79366, 79366, 79366, 79366, 79368, 79369, 79371];
expect Sorted(seqint0) && HasAddends(seqint0, 158732), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 158732);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 158732;
}

// REPEAT 10 - TIME: 25.9785804 s
