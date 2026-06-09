
method {:test} Test14() {
var seqint0 : seq<int> := [0, 6, 0, 0, 0, 0, 0, 10];
var seqint1 : seq<int> := [12, 2, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 3 - TIME: 8.2657222 s