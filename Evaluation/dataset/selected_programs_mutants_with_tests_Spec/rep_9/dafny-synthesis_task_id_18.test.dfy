
method {:test} Test8() {
var r0 := RemoveChars("\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}", "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0");
expect |r0| <= |"\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}" && !(r0[i] in "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0");
expect forall i :: 0 <= i < |"\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"| ==> "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"[i] in "\U{0004}aaaaaaaaaaaa\U{0002}aaaaaa\U{000C}aaaaaaaa\U{0006}aaaaaa\U{0008}aa\naaaaaaa\0" || "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaa\U{0006}\U{0008}"[i] in r0;
}

// REPEAT 9 - TIME: 10.7000426 s