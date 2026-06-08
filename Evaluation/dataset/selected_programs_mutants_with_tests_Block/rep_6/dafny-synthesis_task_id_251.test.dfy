
method {:test} Test5() {
var seqstring0 : seq<string> := ["", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 6.7531478 s