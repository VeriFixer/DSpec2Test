
method {:test} Test4() {
var seqint0 : seq<int> := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10];
var seqint1 : seq<int> := [5, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 5 - TIME: 7.3654354 s