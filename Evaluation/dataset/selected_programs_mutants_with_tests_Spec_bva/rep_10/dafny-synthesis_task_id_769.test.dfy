
method {:test} Test21() {
var seqint0 : seq<int> := [46, 0, 0, 0, 0, 0, 0, 36, 0, 60];
var seqint1 : seq<int> := [62, 0, 0, 52, 56];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 10 - TIME: 15.2156757 s