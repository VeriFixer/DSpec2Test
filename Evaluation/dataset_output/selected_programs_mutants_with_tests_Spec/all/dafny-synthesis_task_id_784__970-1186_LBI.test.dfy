// dafny-synthesis_task_id_784.dfy

predicate IsEven(n: int)
{
  n % 2 == 0
}

predicate IsOdd(n: int)
{
  n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
  requires 0 <= evenIndex < |lst|
  requires IsEven(lst[evenIndex])
{
  forall i :: 
    0 <= i < evenIndex ==>
      IsOdd(lst[i])
}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
  requires 0 <= oddIndex < |lst|
  requires IsOdd(lst[oddIndex])
{
  forall i :: 
    0 <= i < oddIndex ==>
      IsEven(lst[i])
}

method {:testEntry} FirstEvenOddIndices(lst: seq<int>) returns (evenIndex: int, oddIndex: int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= evenIndex < |lst|
  ensures 0 <= oddIndex < |lst|
  ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
  ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> IsOdd(lst[j])
  {
    break;
    if IsEven(lst[i]) {
      evenIndex := i;
      break;
    }
  }
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> IsEven(lst[j])
  {
    if IsOdd(lst[i]) {
      oddIndex := i;
      break;
    }
  }
}

method {:testEntry} ProductEvenOdd(lst: seq<int>) returns (product: int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
  var evenIndex, oddIndex := FirstEvenOddIndices(lst);
  product := lst[evenIndex] * lst[oddIndex];
}


method {:test} Test0() {
var seqint0 : seq<int> := [17890, 1219, 0, 0, 0, 0, 0, 16197, 0, 0, 562, 4565];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [0, 1735];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 1 - TIME: 27.449893 s

method {:test} Test2() {
var seqint0 : seq<int> := [9358, 0, 0, 17891, 4564, 1071, 0, 0, 17710, 2285];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 4565, 0, 0, 0, 0, 0, 0, 0, 3593];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 2 - TIME: 50.3071118 s

method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 3776, 4481, 0, 0, 11840, 0, 0, 16913, 5994, 0, 16731];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [2, 1];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 3 - TIME: 73.0583104 s

method {:test} Test6() {
var seqint0 : seq<int> := [9366, 5233];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [11964, 1070, 0, 0, 0, 1];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 4 - TIME: 95.3868405 s

method {:test} Test8() {
var seqint0 : seq<int> := [1181, 15258, 0, 0, 0, 0, 0, 0, 0, 0, 11707, 3306, 0, 2217, 0, 0, 4657, 13853];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [11076, 11700, 0, 0, 3776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15134];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 5 - TIME: 118.6982877 s

method {:test} Test10() {
var seqint0 : seq<int> := [7218, 5994, 2285, 1219, 0, 0, 0, 0, 0, 3776, 4480, 0, 4892];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [0, 11840, 1181];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 6 - TIME: 141.1252445 s

method {:test} Test12() {
var seqint0 : seq<int> := [4564, 9358, 0, 11707, 0, 3, 0, 0, 0, 0, 3306, 0, 0, 19450];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 16809, 0, 1219, 12566, 0, 8192];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 7 - TIME: 164.0482249 s

method {:test} Test14() {
var seqint0 : seq<int> := [19062, 9358, 17891, 0, 0, 0, 0, 0, 0, 0, 19450, 11707, 1180, 3306, 5232];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [18590, 1, 10378, 6424, 11841];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 8 - TIME: 184.1833637 s

method {:test} Test16() {
var seqint0 : seq<int> := [11841, 3776, 0, 0, 0, 0, 0, 5995, 16912, 2285, 145, 143, 147, 4481, 4893, 150];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [13757, 0, 5994, 4551, 0, 2471];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 9 - TIME: 200.9110995 s

method {:test} Test18() {
var seqint0 : seq<int> := [15772, 9358, 2646, 0, 0, 0, 0, 17891, 3306, 11707, 19450];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [9630, 1, 0, 0, 0, 3296, 1952, 4662, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1071, 3300];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 10 - TIME: 216.355306 s
