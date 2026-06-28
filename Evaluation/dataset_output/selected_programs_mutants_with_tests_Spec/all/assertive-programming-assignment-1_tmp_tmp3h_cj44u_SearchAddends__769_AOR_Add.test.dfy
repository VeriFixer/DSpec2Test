// assertive-programming-assignment-1_tmp_tmp3h_cj44u_SearchAddends.dfy

method {:testEntry} Main()
{
  var q := [1, 2, 4, 5, 6, 7, 10, 23];
  assert Sorted(q);
  assert HasAddends(q, 10) by {
    assert q[2] + q[4] == 4 + 6 == 10;
  }
  var i, j := FindAddends(q, 10);
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
  forall i, j :: 
    0 <= i <= j < |q| ==>
      q[i] <= q[j]
}

predicate HasAddends(q: seq<int>, x: int)
{
  exists i, j :: 
    0 <= i < j < |q| &&
    q[i] + q[j] == x
}

method {:testEntry} FindAddends(q: seq<int>, x: int)
    returns (i: nat, j: nat)
  requires Sorted(q) && HasAddends(q, x)
  ensures i < j < |q| && q[i] + q[j] == x
{
  i := 0;
  j := |q| + 1;
  var sum := q[i] + q[j];
  while sum != x
    invariant LoopInv(q, x, i, j, sum)
    decreases j - i
  {
    if sum > x {
      LoopInvWhenSumIsBigger(q, x, i, j, sum);
      j := j - 1;
    } else {
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
  HasAddends(q[i .. j + 1], x)
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
  requires sum > x
  requires LoopInv(q, x, i, j, sum)
  ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
  assert q[i .. j] < q[i .. j + 1];
}


method {:test} Test0() {
Main();
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 0), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 0);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 0;
}

// REPEAT 1 - TIME: 5.5946536 s

method {:test} Test2() {
var seqint0 : seq<int> := [5921, 5921, 5921, 5921, 5921, 5921, 5921, 5921, 5921];
expect Sorted(seqint0) && HasAddends(seqint0, 11842), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 11842);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 11842;
}

// REPEAT 2 - TIME: 7.3294842 s

method {:test} Test3() {
var seqint0 : seq<int> := [6457, 6457, 6457, 6457, 6457, 6457, 6457, 6457, 6457, 12377, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 12914), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 12914);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 12914;
}

// REPEAT 3 - TIME: 9.0572332 s

method {:test} Test4() {
var seqint0 : seq<int> := [12378, 12378, 12378, 12378, 12378, 12378, 12378, 12378];
expect Sorted(seqint0) && HasAddends(seqint0, 24756), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 24756);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 24756;
}

// REPEAT 4 - TIME: 10.7568162 s

method {:test} Test5() {
var seqint0 : seq<int> := [21324, 21324, 21324, 21324, 21324, 21324, 21324, 21324, 21324, 21324, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 42648), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 42648);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 42648;
}

// REPEAT 5 - TIME: 12.2246038 s

method {:test} Test6() {
var seqint0 : seq<int> := [26004, 26004, 26004, 26004, 26004, 26004, 26004, 26004, 26004, 26004, 26978, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect Sorted(seqint0) && HasAddends(seqint0, 52008), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 52008);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 52008;
}

// REPEAT 6 - TIME: 13.5382216 s

method {:test} Test7() {
var seqint0 : seq<int> := [31925, 31925, 31925, 31925, 31925, 31925, 31925, 31925, 31925, 32477, 0, 0, 0, 0, 0, 0, 0, 0, 40870];
expect Sorted(seqint0) && HasAddends(seqint0, 63850), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 63850);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 63850;
}

// REPEAT 7 - TIME: 14.8581327 s

method {:test} Test8() {
var seqint0 : seq<int> := [0, 0, 0, 0, 34923, 34923, 34923, 34923, 34923, 34923, 34923, 34923, 0, 0, 0, 0, 0, 0, 34923, 0, 39602];
expect Sorted(seqint0) && HasAddends(seqint0, 69846), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 69846);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 69846;
}

// REPEAT 8 - TIME: 16.1657823 s

method {:test} Test9() {
var seqint0 : seq<int> := [38210, 42889, 42889, 42889, 42889, 0, 0, 0, 0, 0, 0, 42889, 42889, 42889, 42889, 42889, 42889];
expect Sorted(seqint0) && HasAddends(seqint0, 85778), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 85778);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 85778;
}

// REPEAT 9 - TIME: 17.2975418 s

method {:test} Test10() {
var seqint0 : seq<int> := [43864, 43864, 43864, 43864, 43864, 43864, 43864, 43864, 43864, 43864, 48543, 48543, 0, 0, 0, 0, 0, 48543];
expect Sorted(seqint0) && HasAddends(seqint0, 87728), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 87728);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 87728;
}

// REPEAT 10 - TIME: 18.4307654 s
