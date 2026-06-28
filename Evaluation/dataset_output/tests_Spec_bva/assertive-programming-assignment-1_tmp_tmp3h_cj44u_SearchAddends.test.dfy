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
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 0), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 0);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
}
method {:test} Test5() {
var seqint0 : seq<int> := [-50, -50, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -50, -50, -50, -50];
expect Sorted(seqint0) && HasAddends(seqint0, -100), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, -100);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == -100;
}
method {:test} Test6() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50];
expect Sorted(seqint0) && HasAddends(seqint0, 100), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 100);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 100;
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 0), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 0);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 0), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 0);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
}

// REPEAT 1 - TIME: 17.7009217 s

method {:test} Test11() {
var seqint0 : seq<int> := [8996, 8996, 8996, 8996, 8996, 8996, 8996, 8996, 8996, 8996, 8996, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 17992), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 17992);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 17992;
}

// REPEAT 2 - TIME: 19.5263157 s

method {:test} Test12() {
var seqint0 : seq<int> := [17942, 17942, 17942, 17942, 17942, 17942, 17942, 17942];
expect Sorted(seqint0) && HasAddends(seqint0, 35884), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 35884);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 35884;
}

// REPEAT 3 - TIME: 21.1535466 s

method {:test} Test13() {
var seqint0 : seq<int> := [18917, 18917, 18917, 18917, 18917, 18917, 18917, 0, 18917, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18917, 20805, 0, 0, 0, 20805];
expect Sorted(seqint0) && HasAddends(seqint0, 37834), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 37834);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 37834;
}

// REPEAT 4 - TIME: 22.6956345 s

method {:test} Test14() {
var seqint0 : seq<int> := [23597, 23597, 23597, 23597, 23597, 23597, 23597, 23597, 23597, 23597, 0, 0, 0, 0, 0, 0, 0, 0, 23597, 23597, 0, 0, 0, 23597, 0, 23597, 24571, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 47194), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 47194);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 47194;
}

// REPEAT 5 - TIME: 24.2902025 s

method {:test} Test15() {
var seqint0 : seq<int> := [29518, 29518, 29518, 29518, 29518, 29518, 29518, 29518, 29518, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29518, 0, 0, 0, 0, 0, 38463, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 59036), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 59036);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 59036;
}

// REPEAT 6 - TIME: 25.7807967 s

method {:test} Test16() {
var seqint0 : seq<int> := [31407, 31407, 31407, 31407, 31407, 31407, 31407, 31407, 0, 31407, 0, 0, 0, 31407, 0, 0, 0, 0, 31407, 31407, 0, 0, 0, 31407, 0, 31407, 33060, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 62814), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 62814);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 62814;
}

// REPEAT 7 - TIME: 27.3006661 s

method {:test} Test17() {
var seqint0 : seq<int> := [0, 32731, 32731, 32731, 32731, 32731, 32731, 32731, 32731, 32731, 0, 0, 0, 32731, 0, 0, 0, 0, 32731, 32731, 32731, 41610];
expect Sorted(seqint0) && HasAddends(seqint0, 65462), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 65462);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 65462;
}

// REPEAT 8 - TIME: 28.7892261 s

method {:test} Test18() {
var seqint0 : seq<int> := [38636, 38636, 38636, 38636, 38636, 38636, 38636, 38636, 38636, 38636, 38636, 40524];
expect Sorted(seqint0) && HasAddends(seqint0, 77272), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 77272);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 77272;
}

// REPEAT 9 - TIME: 30.592689 s

method {:test} Test19() {
var seqint0 : seq<int> := [47093, 47093, 47093, 47093, 47093, 47093, 47093, 47093, 47093, 47093, 0, 0, 47093, 47093, 0, 0, 0, 0, 47093, 0, 0, 0, 47093, 0, 0, 47093, 47093, 48416];
expect Sorted(seqint0) && HasAddends(seqint0, 94186), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 94186);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 94186;
}

// REPEAT 10 - TIME: 32.5998404 s
