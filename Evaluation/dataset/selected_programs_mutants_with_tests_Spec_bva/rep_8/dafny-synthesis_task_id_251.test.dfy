
method {:test} Test16() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}aaaa\U{0008}a\0\n");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aaaa\U{0006}aaaa\U{0008}a\0\n" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 8 - TIME: 12.4194636 s