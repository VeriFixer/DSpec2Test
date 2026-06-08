
method {:test} Test16() {
var seqint0 : seq<int> := [28, 19, 0, 0, 0, 0, 0, 0, 15, 0, 24];
var seqint1 : seq<int> := [26, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22];
var r0 := Difference(seqint0, seqint1);
expect forall x :: x in r0 <==> x in seqint0 && x !in seqint1;
expect forall i, j :: 0 <= i < j < |r0| ==> r0[i] != r0[j];
}

// REPEAT 5 - TIME: 10.7607175 s