
method {:test} Test12() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 9.6519295 s