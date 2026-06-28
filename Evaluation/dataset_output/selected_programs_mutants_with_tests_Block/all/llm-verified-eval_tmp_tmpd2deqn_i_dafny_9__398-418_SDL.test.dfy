// llm-verified-eval_tmp_tmpd2deqn_i_dafny_9.dfy

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
    if numbers[i] > result {
    }
  }
}

method {:testEntry} rolling_max(numbers: seq<int>) returns (result: seq<int>)
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
var seqint0 : seq<int> := [-6863, 0, 0, 0, 1235, 0, 0, 0, 0, 0, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [5309, 0, 0, 0, 0, 6283, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6283, 15139];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 1 - TIME: 3.1986217 s

method {:test} Test2() {
var seqint0 : seq<int> := [7718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7718, 7719];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [2923, 0, 0, 0, 5920, 0, 5920, 0, 0, 0, 0, 5920, 5921];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 4.7512245 s

method {:test} Test4() {
var seqint0 : seq<int> := [7717, 7719];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [5920, 0, 0, 0, 0, 0, 5920, 14776];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 3 - TIME: 6.4852448 s

method {:test} Test6() {
var seqint0 : seq<int> := [1235, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [6670, 8945, 0, 8945, 17311, 0, 0, 0, 4];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 8.30501 s

method {:test} Test8() {
var seqint0 : seq<int> := [5921, 7719];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [8279, 6483];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}
method {:test} Test10() {
var seqint0 : seq<int> := [7018, 7019, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 9.967444 s

method {:test} Test11() {
var seqint0 : seq<int> := [7437, 0, 0, 7718, 7718, 7718, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7719, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 6];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test12() {
var seqint0 : seq<int> := [-3025, 0, 5920, 13640];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 11.3074986 s

method {:test} Test13() {
var seqint0 : seq<int> := [786, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test14() {
var seqint0 : seq<int> := [1796, 3033];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 12.4188055 s

method {:test} Test15() {
var seqint0 : seq<int> := [1235, 1235, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test16() {
var seqint0 : seq<int> := [1174, -7681];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}
method {:test} Test17() {
var seqint0 : seq<int> := [-286, -285];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 13.7975438 s

method {:test} Test18() {
var seqint0 : seq<int> := [93, 1235, 1235, 1236, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [7817, 0, 8098, 0, 8098, 8098, 0, 7563, 8099, 8945];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 14.8860102 s

method {:test} Test20() {
var seqint0 : seq<int> := [93, 1235, 1236, 0, 0, 535];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test21() {
var seqint0 : seq<int> := [535, 535, 2332, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 15.8491891 s
