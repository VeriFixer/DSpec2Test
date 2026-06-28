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
      continue;
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
var seqint0 : seq<int> := [1218, 1];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test2() {
var seqint0 : seq<int> := [4874, 16197, 0, 0, 0, 899, 0, 11840, 0, 0, 0, 562, 16731];
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
var seqint0 : seq<int> := [2284, 1];
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
var seqint0 : seq<int> := [11707, 2284, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4565];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test6() {
var seqint0 : seq<int> := [4874, 0, 0, 0, 0, 0, 16197, 16731, 17890];
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
var seqint0 : seq<int> := [898, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11841, 0, 0, 0, 0, 0, 16197, 16730];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test8() {
var seqint0 : seq<int> := [0, 1735];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test9() {
var seqint0 : seq<int> := [0, 1];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 4565, 0, 0, 16731, 2284, 0, 0, 0, 0, 0, 0, 0, 11707];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test11() {
var seqint0 : seq<int> := [-100, 1];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test12() {
var seqint0 : seq<int> := [100, 1, 16196];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test13() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2471, 899, 16196];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}
method {:test} Test14() {
var seqint0 : seq<int> := [1070, 1, 11706, 4565];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 1 - TIME: 278.2773148 s
