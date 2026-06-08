
method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0aa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0aa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 6.6990835 s