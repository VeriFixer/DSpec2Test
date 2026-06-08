
method {:test} Test15() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "\U{0004}\U{0002}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0008}\n\U{000C}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "\U{0004}\U{0002}aaaaaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\0aaaaaaaaaa\U{0008}\n\U{000C}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 7 - TIME: 12.2703024 s