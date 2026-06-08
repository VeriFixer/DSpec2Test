
method {:test} Test1() {
var seqstring0 : seq<string> := ["", ""];
var r0 := InsertBeforeEach(seqstring0, "aaaaaaaaaaaaaaaaaaa\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "aaaaaaaaaaaaaaaaaaa\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 2 - TIME: 3.3488873 s