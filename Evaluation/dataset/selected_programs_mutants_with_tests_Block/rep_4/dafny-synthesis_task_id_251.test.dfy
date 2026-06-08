
method {:test} Test3() {
var seqstring0 : seq<string> := ["", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}aaaaaaaaaaa\0aaaaaaa\U{0002}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}aaaaaaaaaaa\0aaaaaaa\U{0002}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 4 - TIME: 4.9408879 s