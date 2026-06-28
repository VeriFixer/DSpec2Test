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
    break;
    if numbers[i] > result {
      result := numbers[i];
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
var seqint0 : seq<int> := [-67, 0, 0, 0, 0, 0, 5853, 0, 5853, 5853, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [861, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 1142, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 1 - TIME: 15.5422794 s

method {:test} Test2() {
var seqint0 : seq<int> := [-533, 0, 609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [861, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 1142];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 28.3708109 s

method {:test} Test4() {
var seqint0 : seq<int> := [7817, 0, 8098, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8098, 0, 0, 0, 0, 0, 0, 8098, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [-254, 281, 0, 0, 0, 0, 0, 0, 0, 0, 281, 0, 281];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 3 - TIME: 41.7069705 s

method {:test} Test6() {
var seqint0 : seq<int> := [328, 0, 609, 0, 0, 609, 609];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [1347, 0, 0, 0, 0, 1796, 0, 0, 1796, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 53.7789825 s

method {:test} Test8() {
var seqint0 : seq<int> := [2662, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5948, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8945, 0, 0, 8945, 0, 8945];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [8084, 0, 8365, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7830];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 65.5001173 s

method {:test} Test10() {
var seqint0 : seq<int> := [609, 0, 609];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 79.2279472 s

method {:test} Test12() {
var seqint0 : seq<int> := [1796, 1796, 0, 1796];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [281, 0, 281, 281, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 95.5943517 s

method {:test} Test14() {
var seqint0 : seq<int> := [449, 449];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [-2245, 0, 0, 0, 0, 5853, 0, 0, 5853, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 108.79914 s

method {:test} Test16() {
var seqint0 : seq<int> := [4711, 0, 5853, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [6956, 0, 0, 0, 0, 8098, 0, 8098, 7817, 0, 0, 0, 8098, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 128.6646239 s

method {:test} Test18() {
var seqint0 : seq<int> := [1796, 0, 1796, -486, 1796];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [8098, 0, 0, 8098, 0, 0, 0, 0, 6956, 0, 8098, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 147.203935 s
