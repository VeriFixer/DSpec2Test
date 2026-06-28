// RollingMax.dfy

function isMax(m: int, numbers: seq<int>): bool
{
  m in numbers &&
  forall i :: 
    0 <= i < |numbers| ==>
      numbers[i] <= m
}

method {:testEntry} max(numbers: seq<int>) returns (result: int)
  requires numbers != []
  ensures isMax(result, numbers)
{
  result := numbers[0];
  for i := 1 to |numbers|
    invariant isMax(result, numbers[0 .. i])
  {
    if false {
      result := numbers[i];
    }
  }
}

method {:testEntry} RollingMax(numbers: seq<int>) returns (result: seq<int>)
  requires numbers != []
  ensures |result| == |numbers|
  ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0 .. i + 1])
{
  var m := numbers[0];
  result := [m];
  for i := 1 to |numbers|
    invariant |result| == i
    invariant m == result[i - 1]
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0 .. j + 1])
  {
    if numbers[i] > m {
      m := numbers[i];
    }
    result := result + [m];
  }
}


method {:test} Test0() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [7719];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test2() {
var seqint0 : seq<int> := [0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, -100];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 100];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test8() {
var seqint0 : seq<int> := [0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}
method {:test} Test14() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 1 - TIME: 39.585826 s

method {:test} Test16() {
var seqint0 : seq<int> := [-7129, -1201, 0, 0, 0, 0, 0, 0, 1236, -560, -1046];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [3, 1, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 43.4860754 s

method {:test} Test18() {
var seqint0 : seq<int> := [787, -1201, 0, 0, 0, 0, 0, 0, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [0, 0, 0, 2, 0, 5, 7];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 3 - TIME: 47.4181931 s

method {:test} Test20() {
var seqint0 : seq<int> := [787, -1201, 0, 0, 0, 0, 0, 0, 1236, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 4, 0, 0, 0, 0, 0, 8, 10];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 51.411022 s

method {:test} Test22() {
var seqint0 : seq<int> := [7720];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test23() {
var seqint0 : seq<int> := [13, 0, 6, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 55.2043424 s

method {:test} Test24() {
var seqint0 : seq<int> := [1236, -1201, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test25() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 14, 17];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 59.0353465 s

method {:test} Test26() {
var seqint0 : seq<int> := [2437, 0, 0, 0, 0, 0, 641];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test27() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 23];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 62.9895157 s

method {:test} Test28() {
var seqint0 : seq<int> := [8574, 7059, 0, 0, 490, 8855, 0, 8406];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test29() {
var seqint0 : seq<int> := [25, 0, 0, 16, 0, 0, 0, 22];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 66.7229637 s

method {:test} Test30() {
var seqint0 : seq<int> := [788, -1201, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test31() {
var seqint0 : seq<int> := [28, 0, 20, 26];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 70.8645611 s

method {:test} Test32() {
var seqint0 : seq<int> := [1796, 0, 0, 0, 1347, 0, 0, 1187, -4057, -6302, 654];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test33() {
var seqint0 : seq<int> := [33, 0, 0, 24, 0, 0, 0, 0, 0, 29, 31];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RollingMax(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 74.8327216 s
