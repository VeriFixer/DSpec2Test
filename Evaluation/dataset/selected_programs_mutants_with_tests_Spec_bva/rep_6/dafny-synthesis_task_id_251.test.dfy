
method {:test} Test14() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0006}\U{0008}\n");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0006}\U{0008}\n" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 6 - TIME: 11.3753376 s