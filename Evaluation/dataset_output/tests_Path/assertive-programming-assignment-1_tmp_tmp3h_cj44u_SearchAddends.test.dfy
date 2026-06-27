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

// REPEAT 1 - TIME: 13.1239075 s

method {:test} Test2() {
var seqint0 : seq<int> := [15716, 15716, 15716, 0, 15716, 0, 15716, 15716, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15716, 0, 0, 0, 0, 0, 0, 0, 15716];
expect Sorted(seqint0) && HasAddends(seqint0, 31432), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 31432);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 31432;
}

// REPEAT 2 - TIME: 18.7555884 s

method {:test} Test3() {
var seqint0 : seq<int> := [7307, 16952, 16952, 16952, 16952, 16952, 16952, 16952, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16952];
expect Sorted(seqint0) && HasAddends(seqint0, 33904), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 33904);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 33904;
}

// REPEAT 3 - TIME: 24.4340562 s

method {:test} Test4() {
var seqint0 : seq<int> := [23879, 23879, 23879, 23879, 23879, 23879, 23879, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23879, 23879];
expect Sorted(seqint0) && HasAddends(seqint0, 47758), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 47758);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 47758;
}

// REPEAT 4 - TIME: 31.1351471 s

method {:test} Test5() {
var seqint0 : seq<int> := [31734, 31734, 31734, 31734, 31734, 31734, 31734, 0, 31734, 0, 0, 0, 0, 0, 31734];
expect Sorted(seqint0) && HasAddends(seqint0, 63468), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 63468);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 63468;
}

// REPEAT 5 - TIME: 36.9216239 s

method {:test} Test6() {
var seqint0 : seq<int> := [33058, 33058, 33058, 33058, 33058, 33058, 33058, 33058, 33058, 0, 0, 0, 0, 33058];
expect Sorted(seqint0) && HasAddends(seqint0, 66116), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 66116);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 66116;
}

// REPEAT 6 - TIME: 41.9831219 s

method {:test} Test7() {
var seqint0 : seq<int> := [35982, 45513, 45513, 45513, 45513, 45513, 45513, 45513, 45513, 45513, 45513];
expect Sorted(seqint0) && HasAddends(seqint0, 91026), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 91026);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 91026;
}

// REPEAT 7 - TIME: 49.2689812 s

method {:test} Test8() {
var seqint0 : seq<int> := [54100, 54100, 54100, 54100, 0, 0, 54100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54100, 54100, 0, 0, 54100, 0, 54100, 54100, 54100];
expect Sorted(seqint0) && HasAddends(seqint0, 108200), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 108200);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 108200;
}

// REPEAT 8 - TIME: 56.9686371 s

method {:test} Test9() {
var seqint0 : seq<int> := [55754, 55754, 55754, 55754, 55754, 55754, 55754, 0, 0, 55754];
expect Sorted(seqint0) && HasAddends(seqint0, 111508), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 111508);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 111508;
}

// REPEAT 9 - TIME: 63.5701682 s

method {:test} Test10() {
var seqint0 : seq<int> := [59890, 59890, 59890, 59890, 59890, 59890, 59890, 0, 0, 0, 0, 59890, 0, 0, 59890, 59890, 59890, 59890, 59890, 59890, 59890, 59890];
expect Sorted(seqint0) && HasAddends(seqint0, 119780), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 119780);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 119780;
}

// REPEAT 10 - TIME: 72.5139356 s
