
method {:test} Test17() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaaaa\0aaaaaaaa\U{0008}\naa\U{000C}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}aaaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaaaa\0aaaaaaaa\U{0008}\naa\U{000C}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 9 - TIME: 13.3002484 s