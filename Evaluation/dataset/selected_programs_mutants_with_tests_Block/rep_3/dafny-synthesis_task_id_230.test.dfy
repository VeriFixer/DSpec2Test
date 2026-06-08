
method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("a\U{0001}a", '\0');
expect |r0| == |"a\U{0001}a"|;
expect forall i :: 0 <= i < |"a\U{0001}a"| ==> ("a\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}a"[i] != ' ' ==> r0[i] == "a\U{0001}a"[i]);
}
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar(" aa", '\0');
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (" aa"[i] == ' ' ==> r0[i] == '\0') && (" aa"[i] != ' ' ==> r0[i] == " aa"[i]);
}

// REPEAT 3 - TIME: 5.8769388 s