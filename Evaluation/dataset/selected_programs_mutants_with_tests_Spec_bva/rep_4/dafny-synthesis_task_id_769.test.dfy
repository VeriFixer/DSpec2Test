
method {:test} Test15() {
var seqint0 : seq<int> := [18, 11, 0];
var seqint1 : seq<int> := [16, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 4 - TIME: 10.0304301 s