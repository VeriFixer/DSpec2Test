
method {:test} Test18() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0008}\n\U{0002}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaaa\U{0004}\U{0006}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 14.0260107 s