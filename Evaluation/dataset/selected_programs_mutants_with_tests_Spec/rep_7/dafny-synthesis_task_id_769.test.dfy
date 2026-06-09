
method {:test} Test6() {
var seqint0 : seq<int> := [21];
var seqint1 : seq<int> := [17, 12, 0];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 7 - TIME: 8.5423075 s