
method {:test} Test4() {
var seqstring0 : seq<string> := ["", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaa\0aaaaaaaaaaa\U{0002}\U{0004}");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaa\0aaaaaaaaaaa\U{0002}\U{0004}" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 5 - TIME: 5.8339537 s