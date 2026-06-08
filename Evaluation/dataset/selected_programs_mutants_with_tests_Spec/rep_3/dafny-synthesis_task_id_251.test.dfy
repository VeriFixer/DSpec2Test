
method {:test} Test2() {
var seqstring0 : seq<string> := ["", "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", ""];
var r0 := InsertBeforeEach(seqstring0, "a\0");
expect |r0| == 2 * |seqstring0|;
expect forall i :: 0 <= i < |seqstring0| ==> r0[2 * i] == "a\0" && r0[2 * i + 1] == seqstring0[i];
}

// REPEAT 3 - TIME: 4.647674 s