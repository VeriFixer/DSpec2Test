
method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 7.6359907 s