
method {:test} Test9() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}\U{0002}a\0a");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}\U{0002}a\0a" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 10 - TIME: 9.6398996 s