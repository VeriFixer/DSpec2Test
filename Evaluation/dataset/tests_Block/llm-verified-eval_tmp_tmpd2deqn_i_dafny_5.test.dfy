method {:testEntry} intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    for i := 0 to |numbers|
    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> 
                interspersed[i0] == numbers[i0 / 2]
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==>
                interspersed[i0] == delimiter
    {
        if i > 0 {
            interspersed := interspersed + [delimiter];
        }
        interspersed := interspersed + [numbers[i]];
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [0];
var r0 := intersperse(seqint0, 0);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 0;
}

// REPEAT 1 - TIME: 3.0761347 s

method {:test} Test2() {
var seqint0 : seq<int> := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3];
var r0 := intersperse(seqint0, 24);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 24;
}
method {:test} Test3() {
var seqint0 : seq<int> := [1, 0];
var r0 := intersperse(seqint0, 25);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 25;
}

// REPEAT 2 - TIME: 4.4476616 s

method {:test} Test4() {
var seqint0 : seq<int> := [2, 0];
var r0 := intersperse(seqint0, 26);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 26;
}
method {:test} Test5() {
var seqint0 : seq<int> := [2];
var r0 := intersperse(seqint0, 26);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 26;
}

// REPEAT 3 - TIME: 5.744191 s

method {:test} Test6() {
var seqint0 : seq<int> := [4];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}
method {:test} Test7() {
var seqint0 : seq<int> := [4, 0, 0];
var r0 := intersperse(seqint0, 27);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 27;
}

// REPEAT 4 - TIME: 6.8981519 s

method {:test} Test8() {
var seqint0 : seq<int> := [5, 0, 0, 0];
var r0 := intersperse(seqint0, 29);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 29;
}
method {:test} Test9() {
var seqint0 : seq<int> := [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
var r0 := intersperse(seqint0, 28);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 28;
}

// REPEAT 5 - TIME: 7.9172191 s

method {:test} Test10() {
var seqint0 : seq<int> := [6];
var r0 := intersperse(seqint0, 46);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 46;
}
method {:test} Test11() {
var seqint0 : seq<int> := [6, 0, 0, 0, 0, 0, 0, 0, 0, 9, 13, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15];
var r0 := intersperse(seqint0, 47);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 47;
}

// REPEAT 6 - TIME: 8.9644145 s

method {:test} Test12() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20];
var r0 := intersperse(seqint0, 48);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 48;
}
method {:test} Test13() {
var seqint0 : seq<int> := [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 22, 0, 0, 0, 0, 20, 0, 16, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 49);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 49;
}

// REPEAT 7 - TIME: 10.0334558 s

method {:test} Test14() {
var seqint0 : seq<int> := [10, 0, 0, 17, 21];
var r0 := intersperse(seqint0, 50);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 50;
}
method {:test} Test15() {
var seqint0 : seq<int> := [10, 0, 17, 0, 0, 0, 0, 0, 21, 0, 0, 0, 24];
var r0 := intersperse(seqint0, 50);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 50;
}

// REPEAT 8 - TIME: 11.188875 s

method {:test} Test16() {
var seqint0 : seq<int> := [14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 51);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 51;
}
method {:test} Test17() {
var seqint0 : seq<int> := [14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0];
var r0 := intersperse(seqint0, 51);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 51;
}

// REPEAT 9 - TIME: 12.3893926 s

method {:test} Test18() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 33];
var r0 := intersperse(seqint0, 52);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 52;
}
method {:test} Test19() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31];
var r0 := intersperse(seqint0, 52);
expect |r0| == if |seqint0| > 0 then 2 * |seqint0| - 1 else 0;
expect forall i :: 0 <= i < |r0| ==> i % 2 == 0 ==> r0[i] == seqint0[i / 2];
expect forall i :: 0 <= i < |r0| ==> i % 2 == 1 ==> r0[i] == 52;
}

// REPEAT 10 - TIME: 13.8058435 s
