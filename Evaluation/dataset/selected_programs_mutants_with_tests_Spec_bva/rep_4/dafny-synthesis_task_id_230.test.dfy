
method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("aaa", '\0');
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> ("aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaa"[i] != ' ' ==> r0[i] == "aaa"[i]);
}

// REPEAT 4 - TIME: 8.8266776 s