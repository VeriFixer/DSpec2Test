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
var seqint0 : seq<int> := [-5975, 13475, 0, 0, 13475, 13475, 0, 0, 0, 0, 13475, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13475, 13475, 13475, 13475];
expect Sorted(seqint0) && HasAddends(seqint0, 26950), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 26950);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 26950;
}

// REPEAT 1 - TIME: 9.5520784 s

method {:test} Test2() {
var seqint0 : seq<int> := [15687, 15687, 15687, 15687, 15687, 0, 0, 0, 15687, 0, 0, 0, 15687, 0, 15687, 0, 0, 15687];
expect Sorted(seqint0) && HasAddends(seqint0, 31374), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 31374);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 31374;
}

// REPEAT 2 - TIME: 13.6472159 s

method {:test} Test3() {
var seqint0 : seq<int> := [24667, 26907, 0, 0, 0, 0, 0, 26907, 26907, 26907, 26907, 26907, 0, 0, 26907, 26907];
expect Sorted(seqint0) && HasAddends(seqint0, 53814), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 53814);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 53814;
}

// REPEAT 3 - TIME: 17.7706542 s

method {:test} Test4() {
var seqint0 : seq<int> := [27143, 29589, 29589, 29589, 0, 29589, 29589, 0, 29589, 29589, 0, 0, 0, 0, 29589];
expect Sorted(seqint0) && HasAddends(seqint0, 59178), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 59178);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 59178;
}

// REPEAT 4 - TIME: 22.5659142 s

method {:test} Test5() {
var seqint0 : seq<int> := [31651, 31651, 31651, 31651, 31651, 31651, 31651, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31651];
expect Sorted(seqint0) && HasAddends(seqint0, 63302), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 63302);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 63302;
}

// REPEAT 5 - TIME: 27.6595571 s

method {:test} Test6() {
var seqint0 : seq<int> := [39873, 39873, 39873, 39873, 39873, 39873, 39873, 39873, 39873, 39873, 0, 0, 39873];
expect Sorted(seqint0) && HasAddends(seqint0, 79746), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 79746);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 79746;
}

// REPEAT 6 - TIME: 32.9957204 s

method {:test} Test7() {
var seqint0 : seq<int> := [47452, 47452, 47452, 47452, 47452, 0, 47452, 0, 0, 0, 47452, 47452];
expect Sorted(seqint0) && HasAddends(seqint0, 94904), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 94904);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 94904;
}

// REPEAT 7 - TIME: 38.2899731 s

method {:test} Test8() {
var seqint0 : seq<int> := [57178, 57178, 57178, 57178, 57178, 57178, 57178, 57178, 57178, 0, 57178];
expect Sorted(seqint0) && HasAddends(seqint0, 114356), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 114356);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 114356;
}

// REPEAT 8 - TIME: 43.5127951 s

method {:test} Test9() {
var seqint0 : seq<int> := [66058, 66058, 66058, 66058, 66058, 66058, 66058, 66058, 0, 0, 66058, 66058];
expect Sorted(seqint0) && HasAddends(seqint0, 132116), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 132116);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 132116;
}

// REPEAT 9 - TIME: 48.7029739 s

method {:test} Test10() {
var seqint0 : seq<int> := [67035, 67035, 67035, 67035, 67035, 67035, 0, 0, 0, 0, 0, 67035, 67035];
expect Sorted(seqint0) && HasAddends(seqint0, 134070), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 134070);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 134070;
}

// REPEAT 10 - TIME: 54.829662 s
