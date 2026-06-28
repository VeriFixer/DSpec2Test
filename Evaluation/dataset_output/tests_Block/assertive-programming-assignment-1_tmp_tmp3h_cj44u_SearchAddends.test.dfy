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

// REPEAT 1 - TIME: 5.6362267 s

method {:test} Test3() {
var seqint0 : seq<int> := [21835, 21836, 21836, 21836, 21836, 21836, 21836, 21836, 21836, 21836, 25342, 25342, 0, 0, 0, 0, 25342];
expect Sorted(seqint0) && HasAddends(seqint0, 43672), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 43672);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 43672;
}
method {:test} Test4() {
var seqint0 : seq<int> := [18140, 18147, 18147, 18147, 18147, 18148, 18149, 18153];
expect Sorted(seqint0) && HasAddends(seqint0, 36294), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 36294);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 36294;
}

// REPEAT 2 - TIME: 7.7624415 s

method {:test} Test5() {
var seqint0 : seq<int> := [31239, 31239, 31239, 31239, 31239, 31239, 31240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31241, 31241, 31241, 0, 0, 31241];
expect Sorted(seqint0) && HasAddends(seqint0, 62478), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 62478);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 62478;
}
method {:test} Test6() {
var seqint0 : seq<int> := [22456, 22461, 22461, 22461, 22461, 22464, 0, 0, 0, 0, 0, 0, 22464, 22464, 22465, 22465];
expect Sorted(seqint0) && HasAddends(seqint0, 44922), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 44922);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 44922;
}

// REPEAT 3 - TIME: 9.788956 s

method {:test} Test7() {
var seqint0 : seq<int> := [35922, 35922, 35923, 35923, 35923, 35923, 35923, 35923, 35923, 35923, 35923, 35925, 35925, 0, 0, 35925];
expect Sorted(seqint0) && HasAddends(seqint0, 71846), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 71846);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 71846;
}
method {:test} Test8() {
var seqint0 : seq<int> := [33470, 33475, 33475, 33475, 33475, 33475, 33475, 33477, 33478, 33479, 0, 0, 0, 33479];
expect Sorted(seqint0) && HasAddends(seqint0, 66950), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 66950);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 66950;
}

// REPEAT 4 - TIME: 11.6574554 s

method {:test} Test9() {
var seqint0 : seq<int> := [43296, 43297, 43297, 43297, 43297, 43297, 43297, 43297, 43297, 50475, 50475, 50475, 50475, 50475, 0, 0, 0, 50475];
expect Sorted(seqint0) && HasAddends(seqint0, 86594), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 86594);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 86594;
}
method {:test} Test10() {
var seqint0 : seq<int> := [35904, 36514, 36514, 36514, 36514, 36514, 36514, 0, 36514, 0, 0, 0, 0, 0, 36514, 36514, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36514, 0, 36514, 0, 36514];
expect Sorted(seqint0) && HasAddends(seqint0, 73028), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 73028);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 73028;
}

// REPEAT 5 - TIME: 13.9067822 s

method {:test} Test11() {
var seqint0 : seq<int> := [48047, 48494, 0, 0, 0, 0, 0, 0, 0, 48495, 48896, 48896, 0, 0, 48896, 48896, 48896, 48896, 48896, 0, 48896, 0, 48896, 48896, 48896, 0, 49297, 49766, 49767];
expect Sorted(seqint0) && HasAddends(seqint0, 97792), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 97792);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 97792;
}
method {:test} Test12() {
var seqint0 : seq<int> := [44616, 44617, 44618, 44619, 44620, 44621, 44621, 44621, 44621, 44621, 44621, 0, 44621];
expect Sorted(seqint0) && HasAddends(seqint0, 89242), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 89242);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 89242;
}

// REPEAT 6 - TIME: 16.2175026 s

method {:test} Test13() {
var seqint0 : seq<int> := [57761, 57762, 57763, 57764, 57765, 57766, 57766, 0, 0, 0, 0, 0, 0, 0, 57766, 57766, 57766, 57766, 57766, 57766, 57772, 0, 0, 0, 57772];
expect Sorted(seqint0) && HasAddends(seqint0, 115532), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 115532);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 115532;
}
method {:test} Test14() {
var seqint0 : seq<int> := [48895, 48897, 48897, 48897, 48898];
expect Sorted(seqint0) && HasAddends(seqint0, 97794), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 97794);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 97794;
}

// REPEAT 7 - TIME: 18.4115302 s

method {:test} Test15() {
var seqint0 : seq<int> := [58044, 58046, 58048, 58050, 58051, 0, 58052, 58052, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58052];
expect Sorted(seqint0) && HasAddends(seqint0, 116096), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 116096);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 116096;
}
method {:test} Test16() {
var seqint0 : seq<int> := [65621, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 65621, 67272, 67273, 67273];
expect Sorted(seqint0) && HasAddends(seqint0, 131242), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 131242);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 131242;
}

// REPEAT 8 - TIME: 20.7359387 s

method {:test} Test17() {
var seqint0 : seq<int> := [68425, 68425, 0, 68426, 68426, 68426, 68426, 68426, 68426, 68426, 68426, 68426, 68426, 68426, 68427, 68428, 68429];
expect Sorted(seqint0) && HasAddends(seqint0, 136852), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 136852);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 136852;
}
method {:test} Test18() {
var seqint0 : seq<int> := [69717, 69718, 0, 0, 0, 0, 0, 0, 69718, 69718, 69718, 0, 0, 0, 0, 0, 69718, 69718, 69718, 69718, 69718, 0, 69718, 0, 0, 0, 69718, 69718, 69718, 69718];
expect Sorted(seqint0) && HasAddends(seqint0, 139436), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 139436);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 139436;
}

// REPEAT 9 - TIME: 23.4060958 s

method {:test} Test19() {
var seqint0 : seq<int> := [70820, 70821, 0, 0, 70821, 70821, 70821, 70821, 70821, 0, 70821, 0, 0, 0, 0, 0, 0, 0, 0, 70821, 70823, 0, 0, 0, 0, 70823];
expect Sorted(seqint0) && HasAddends(seqint0, 141642), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 141642);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 141642;
}
method {:test} Test20() {
var seqint0 : seq<int> := [63462, 79250, 0, 0, 0, 79250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79250, 79250, 0, 79250, 0, 79250, 79250, 79250, 79250, 79250];
expect Sorted(seqint0) && HasAddends(seqint0, 158500), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 158500);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 158500;
}

// REPEAT 10 - TIME: 26.0608999 s
