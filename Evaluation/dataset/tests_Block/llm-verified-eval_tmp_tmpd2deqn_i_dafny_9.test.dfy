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
var seqint0 : seq<int> := [-4618, 0, 0, 1235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test1() {
var seqint0 : seq<int> := [5309, 0, 0, 0, 0, 0, 0, 0, 0, 6283, 15139];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 1 - TIME: 3.414732 s

method {:test} Test2() {
var seqint0 : seq<int> := [-4618, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 0, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test3() {
var seqint0 : seq<int> := [2923, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5920, 0, 5920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5920, 5921];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 2 - TIME: 5.1040974 s

method {:test} Test4() {
var seqint0 : seq<int> := [1235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 0, 0, 0, 1235, 0, 0, 0, 0, 0, 0, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test5() {
var seqint0 : seq<int> := [4266, 8945, 0, 0, 0, 0, 0, 0, 8945, 8946, 0, 4];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 3 - TIME: 6.5149084 s

method {:test} Test6() {
var seqint0 : seq<int> := [1235, 1235, 1236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 5];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test7() {
var seqint0 : seq<int> := [7029, 5173, 7619, 7619, 0, 0, 7619, 0, 9860, 0, 0, 6];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 4 - TIME: 8.0553972 s

method {:test} Test8() {
var seqint0 : seq<int> := [-6863, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 0, 1235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1236, 0, 0, 0, 0, 6, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test9() {
var seqint0 : seq<int> := [5920, 0, 5920, 13640];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 5 - TIME: 9.4215648 s

method {:test} Test10() {
var seqint0 : seq<int> := [700, 0, 1235, 1236];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test11() {
var seqint0 : seq<int> := [535, 535, 536, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 6 - TIME: 10.6066963 s

method {:test} Test12() {
var seqint0 : seq<int> := [1235, 1235, 1236, 0, 4];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test13() {
var seqint0 : seq<int> := [-5748, 535, 9391, 0, 5, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 7 - TIME: 11.8456812 s

method {:test} Test14() {
var seqint0 : seq<int> := [1235, 0, 0, 0, 0, 0, 0, 0, 0, 1235, 1236, 0, 1142];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test15() {
var seqint0 : seq<int> := [5309, 0, 6283, 6283, 6284, 7];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 8 - TIME: 12.8117268 s

method {:test} Test16() {
var seqint0 : seq<int> := [-4669, 0, 0, 1235, 1236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 8, 0, 0, 0, 12, 14];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test17() {
var seqint0 : seq<int> := [1796, 3033];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 9 - TIME: 13.8332155 s

method {:test} Test18() {
var seqint0 : seq<int> := [-7483, 0, 973, 973, 973, 974, 0, 0];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := max(seqint0);
expect isMax(r0, seqint0);
}
method {:test} Test19() {
var seqint0 : seq<int> := [5920, 5920, 5921];
expect seqint0 != [], "If this check fails at runtime, the test does not meet the preconditions";
var r0 := rolling_max(seqint0);
expect |r0| == |seqint0|;
expect forall i :: 0 < i < |r0| ==> isMax(r0[i], seqint0[0 .. i + 1]);
}

// REPEAT 10 - TIME: 14.8637886 s
