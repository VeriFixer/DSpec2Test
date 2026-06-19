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

// REPEAT 1 - TIME: 2.9189395 s

method {:test} Test1() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 2 - TIME: 3.822202 s

method {:test} Test2() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
var seqint1 : seq<int> := [0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 3 - TIME: 4.767092 s

method {:test} Test3() {
var seqint0 : seq<int> := [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9];
var seqint1 : seq<int> := [0, 3, 5];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 4 - TIME: 5.805053 s

method {:test} Test4() {
var seqint0 : seq<int> := [17, 0, 0, 0, 0, 0, 4, 0, 0, 0, 15];
var seqint1 : seq<int> := [0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 13];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 5 - TIME: 6.9526054 s

method {:test} Test5() {
var seqint0 : seq<int> := [19, 0, 0, 0, 0, 0, 0, 6];
var seqint1 : seq<int> := [16, 12];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 6 - TIME: 7.8579329 s

method {:test} Test6() {
var seqint0 : seq<int> := [27, 0, 0, 0, 0, 0, 0, 0, 18];
var seqint1 : seq<int> := [25, 10, 21, 23];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 7 - TIME: 8.898021 s

method {:test} Test7() {
var seqint0 : seq<int> := [31, 0, 0, 0, 0, 0, 0, 0, 0, 26];
var seqint1 : seq<int> := [14, 0, 0, 22, 0, 0, 0, 0, 0, 0, 29];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 8 - TIME: 9.7158505 s

method {:test} Test8() {
var seqint0 : seq<int> := [52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 42, 38, 20, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 50];
var seqint1 : seq<int> := [32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 36, 0, 0, 46, 0, 34, 0, 0, 0, 48];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 9 - TIME: 10.4865084 s

method {:test} Test9() {
var seqint0 : seq<int> := [59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57];
var seqint1 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 33, 0, 41, 0, 0, 0, 24, 53, 0, 37, 0, 55];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 10 - TIME: 11.2097364 s
