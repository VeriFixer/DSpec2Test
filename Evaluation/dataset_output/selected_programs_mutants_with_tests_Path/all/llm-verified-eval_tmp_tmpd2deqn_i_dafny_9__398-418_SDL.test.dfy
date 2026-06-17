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


function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

method {:testEntry} max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
    result := numbers[0];
    for i := 1 to |numbers|
    invariant isMax(result, numbers[0..i])
    {
        if numbers[i] > result {
            result := numbers[i];
        }
    }
}

method {:testEntry} rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    var m := numbers[0];
    result := [m];
    for i := 1 to |numbers|
    invariant |result| == i
    invariant m == result[i-1]
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0..(j+1)])
    {
        if numbers[i] > m {
            m := numbers[i];
        }
        result := result + [m];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [5572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [861, 0, 1142, 0, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 1 - TIME: 14.8686739 s

method {:test} Test2() {
var seqint0 : seq<int> := [5572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 5853, 0, 0, 5853];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [8365, 0, 0, 0, 0, 0, 0, 8365, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2082];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 25.9520001 s

method {:test} Test4() {
var seqint0 : seq<int> := [-67, 0, 0, 0, 0, 5853, 0, 0, 0, 0, 0, 0, 0, 5853];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [1347, 1796, 1796, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 3 - TIME: 37.8574787 s

method {:test} Test6() {
var seqint0 : seq<int> := [1796, 0, 0, 0, 0, 1796, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1796, 0, 1187];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [3705, 4679, 0, 0, 0, 0, 0, 4679, 0, 0, 0, 0, 0, 0, 4679, 0, 0, 0, 0, 2791];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 51.5763447 s

method {:test} Test8() {
var seqint0 : seq<int> := [-7489, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 609, 0, 0, 0, 609, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [-2245, 0, 0, 0, 0, 0, 0, 5853, 0, 0, 5853, 0, 0, 0, 0, 5853, 0, 4711];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 66.069808 s

method {:test} Test10() {
var seqint0 : seq<int> := [267, 0, 8365, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8365, 0, 8365, 0, 0, 7223];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [-7489, 0, 0, 609, 0, 0, 0, 609, 0, 0, 0, 0, 0, 0, 0, 609, -533, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 78.6966817 s

method {:test} Test12() {
var seqint0 : seq<int> := [-533, 0, 609, 0, 0, 609, 609, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [861, 0, 0, 0, 1142, 1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 607, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 93.2853875 s

method {:test} Test14() {
var seqint0 : seq<int> := [2178, 8098, 8098, 0, 0, 0, 0, 8098, 0, 0, 0, -847, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [-4144, 0, 0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, -439, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 122.1006436 s

method {:test} Test16() {
var seqint0 : seq<int> := [328, 0, 609, 0, 0, 609, 0, 0, 609, 0, 0, 74];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [1142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1142, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 151.301644 s

method {:test} Test18() {
var seqint0 : seq<int> := [7563, 8098, 8098, 0, 8098, 0, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [2662, 0, 0, 8945, 0, 0, 0, 0, 8945, 0, 0, 0, 0, 0, 5948, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8945, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 192.1164867 s
