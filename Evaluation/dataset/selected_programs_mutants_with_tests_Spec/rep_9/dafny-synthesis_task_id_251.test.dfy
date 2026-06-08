
method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 10.2152332 s