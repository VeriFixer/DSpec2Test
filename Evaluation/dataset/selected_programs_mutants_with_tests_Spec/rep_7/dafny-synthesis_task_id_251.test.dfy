
method {:test} Test6() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0006}\0\U{0002}\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0006}\0\U{0002}\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 7.530371 s