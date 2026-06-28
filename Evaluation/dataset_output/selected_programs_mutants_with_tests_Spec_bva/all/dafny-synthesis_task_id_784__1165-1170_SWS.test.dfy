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
      break;
      evenIndex := i;
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

method {:test} Test15() {
var seqint0 : seq<int> := [563, 4564, 0, 133, 0, 3306, 0, 17891, 9358, 4481];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test16() {
var seqint0 : seq<int> := [1180, 3306, 1, 1071, 19450, 0, 0, 0, 0, 1219, 0, 0, 0, 12566, 0, 0, 0, 0, 0, 0, 13812];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 2 - TIME: 291.8321885 s

method {:test} Test17() {
var seqint0 : seq<int> := [8270, 0, 0, 0, 0, 0, 0, 15259, 13756, 19450, 2217];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test18() {
var seqint0 : seq<int> := [17891, 14723, 0, 11937, 2, 16197, 16912];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 3 - TIME: 305.3130757 s

method {:test} Test19() {
var seqint0 : seq<int> := [1735, 16442, 16912, 0, 8773, 3776, 5995];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test20() {
var seqint0 : seq<int> := [0, 2216, 0, 0, 2646, 0, 3189, 0, 0, 0, 0, 0, 16443, 0, 7008, 0, 0, 0, 0, 1948, 4656];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 4 - TIME: 319.1826191 s

method {:test} Test21() {
var seqint0 : seq<int> := [11841, 1218, 0, 0, 0, 0, 0, 164, 0, 0, 167, 169, 0, 171, 0, 3776, 16912, 161, 0, 0, 5995, 2285, 0, 0, 0, 0, 4480];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test22() {
var seqint0 : seq<int> := [12778, 0, 0, 9358, 15046, 1, 11962, -5, -1, 0, 17492, 16442, 2783];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 5 - TIME: 332.7526869 s

method {:test} Test23() {
var seqint0 : seq<int> := [4656, 19063, 0, 0, 0, 5233, 15773, 2646, 0, 197, 4422, 200, 202, 14130];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test24() {
var seqint0 : seq<int> := [15772, 0, 0, 0, 5232, 0, 0, 19450, 0, 1071, 0, 12567, 0, 2285, 4422, 0, 1948, 2646, 0, 1180, 14130, 0];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 6 - TIME: 346.2025803 s

method {:test} Test25() {
var seqint0 : seq<int> := [18540, 0, 0, 0, 13405, 3300, 16006, 16913, 3636, 5494, 8642, 15708];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test26() {
var seqint0 : seq<int> := [13056, 0, 1, 11196, 0, 16808, 4225];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 7 - TIME: 359.9274439 s

method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 11706, 13757, 0, 0, 228, 230, 0, 232, 234, 3188, 0, 0, 0, 0, 0, 235, 224, 0, 0, 0, 4911, 4550, 15258, 2216, 9359];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test28() {
var seqint0 : seq<int> := [11883, 17739, 0, 5994, 0, 4657];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 8 - TIME: 373.4357004 s

method {:test} Test29() {
var seqint0 : seq<int> := [4657, 7008, 0, 0, 15772, 13813, 1181, 19062];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test30() {
var seqint0 : seq<int> := [478, 0, 11883, 0, 13405, 0, 4910, 0, 0, 17738, 4550, 0, 6304, 563, 17870, 2470, 0, 3188, 0, 0, 1062, 3146, 1248];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 9 - TIME: 387.053658 s

method {:test} Test31() {
var seqint0 : seq<int> := [2647, 4564, 0, 0, 0, 0, 0, 17891, 3306, 0, 0, 268, 269, 0, 9358, 0, 0, 0, 0, 11707, 0, 0, 0, 0, 0, 0, 0, 275];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := FirstEvenOddIndices(seqint0);
expect 0 <= r0 < |seqint0|;
expect 0 <= r1 < |seqint0|;
expect IsEven(seqint0[r0]) && IsFirstEven(r0, seqint0);
expect IsOdd(seqint0[r1]) && IsFirstOdd(r1, seqint0);
}
method {:test} Test32() {
var seqint0 : seq<int> := [0, 0, 0, 3385, 13516, 17172, 14747, 0, 0, 0, 0, 0, 0, 16936, 17642, 5608, 0, 0, 0, 0, 2902, 1438, 7004];
expect |seqint0| >= 2, "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsEven(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
expect exists i :: 0 <= i < |seqint0| && IsOdd(seqint0[i]), "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ProductEvenOdd(seqint0);
expect exists i, j :: 0 <= i < |seqint0| && IsEven(seqint0[i]) && IsFirstEven(i, seqint0) && 0 <= j < |seqint0| && IsOdd(seqint0[j]) && IsFirstOdd(j, seqint0) && r0 == seqint0[i] * seqint0[j];
}

// REPEAT 10 - TIME: 400.2754958 s
