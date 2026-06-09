
method {:test} Test8() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0002}aaaaaaaaaaaaaaa\0aaaa\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0002}aaaaaaaaaaaaaaa\0aaaa\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 8.2631799 s