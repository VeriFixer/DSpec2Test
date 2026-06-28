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
  j := |q| - 1;
  var sum := q[j];
  while sum != x
    invariant LoopInv(q, x, i, j, sum)
    decreases j - i
  {
    if sum > x {
      LoopInvWhenSumIsBigger(q, x, i, j, sum);
      j := j - 1;
    } else {
      i := 1;
    }
    sum := q[j];
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
  q[j] == x
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

method {:test} Test2() {
var seqint0 : seq<int> := [5921, 5921, 5921, 5921, 5921, 5921, 5921, 5921, 5921];
expect Sorted(seqint0) && HasAddends(seqint0, 11842), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FindAddends(seqint0, 11842);
expect r0 < r1 < |seqint0| && seqint0[r0] + seqint0[r1] == 11842;
}

// REPEAT 2 - TIME: 7.3294842 s
