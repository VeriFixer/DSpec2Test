
method {:test} Test10() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\0\U{0002}a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\0\U{0002}a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 7.8953627 s