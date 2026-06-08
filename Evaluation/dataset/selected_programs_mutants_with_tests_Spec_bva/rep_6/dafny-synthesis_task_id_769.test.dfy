
method {:test} Test17() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 21, 13, 0, 31];
var seqint1 : seq<int> := [33, 0, 0, 25];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 6 - TIME: 11.5551754 s