
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a", '\0');
expect |r0| == |"\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a"|;
expect forall i :: 0 <= i < |"\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a"| ==> ("\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a"[i] != ' ' ==> r0[i] == "\U{0005}aaaaaaaa\U{0001}\U{0003}aaaa\U{0007}a"[i]);
}

// REPEAT 8 - TIME: 8.1975097 s