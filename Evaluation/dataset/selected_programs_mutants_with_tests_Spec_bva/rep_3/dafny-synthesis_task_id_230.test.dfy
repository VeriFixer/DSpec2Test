
method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaa\U{0003}", '\0');
expect |r0| == |"  aaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"  aaaaaaaaa\U{0003}"| ==> ("  aaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "  aaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 8.7237549 s