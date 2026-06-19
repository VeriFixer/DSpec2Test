method {:testEntry} Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{
    diff := [];
    for i := 0 to |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in diff <==> (x in a[..i] && x !in b)
        invariant forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
    {
        if a[i] !in b && a[i] !in diff
        {
            diff := diff + [a[i]];
        }
    }
}

method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}
method {:test} Test2() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}
method {:test} Test3() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}
method {:test} Test5() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}
method {:test} Test6() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 1 - TIME: 7.898778 s

method {:test} Test13() {
var seqint0 : seq<int> := [1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7];
var seqint1 : seq<int> := [0, 5, 0, 0, 0, 0, 0, 0, 0, 9];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 2 - TIME: 8.6006962 s

method {:test} Test14() {
var seqint0 : seq<int> := [0, 6, 0];
var seqint1 : seq<int> := [12, 0, 0, 0, 0, 0, 0, 10, 2];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 3 - TIME: 9.3382816 s

method {:test} Test15() {
var seqint0 : seq<int> := [14, 0, 0, 0];
var seqint1 : seq<int> := [11, 0, 4];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 4 - TIME: 10.0079592 s

method {:test} Test16() {
var seqint0 : seq<int> := [17, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 19, 25];
var seqint1 : seq<int> := [23, 0, 0, 0, 21, 15, 0, 0, 0, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 5 - TIME: 10.5931542 s

method {:test} Test17() {
var seqint0 : seq<int> := [30, 18, 0];
var seqint1 : seq<int> := [28, 0, 13, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 6 - TIME: 11.2967069 s

method {:test} Test18() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 24, 0, 29, 38, 40, 0, 0, 0, 0, 34, 0, 0, 0, 42];
var seqint1 : seq<int> := [0, 16, 36, 32];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 7 - TIME: 12.1195203 s

method {:test} Test19() {
var seqint0 : seq<int> := [53, 0, 0, 0, 20, 0, 0, 0, 31, 0, 43, 0, 0, 0, 0, 0, 0, 0, 51];
var seqint1 : seq<int> := [55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 39, 0, 0, 45, 47, 49];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 8 - TIME: 12.954252 s

method {:test} Test20() {
var seqint0 : seq<int> := [58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [56, 0, 27, 44, 48];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 9 - TIME: 13.7169655 s

method {:test} Test21() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 54, 61, 0, 0, 0, 0, 0, 46, 0, 59, 69, 0, 0, 0, 0, 0];
var seqint1 : seq<int> := [0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 65, 0, 67, 0, 0, 71, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 10 - TIME: 14.4918924 s
