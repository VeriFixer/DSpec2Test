
method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 8.8518169 s