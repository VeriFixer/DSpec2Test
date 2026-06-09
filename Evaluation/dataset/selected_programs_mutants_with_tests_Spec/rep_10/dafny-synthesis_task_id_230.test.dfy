
method {:test} Test9() {
var r0 := ReplaceBlanksWithChar("\U{0005}a\U{0001}\U{0003}", '\0');
expect |r0| == |"\U{0005}a\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0005}a\U{0001}\U{0003}"| ==> ("\U{0005}a\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0005}a\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "\U{0005}a\U{0001}\U{0003}"[i]);
}

// REPEAT 10 - TIME: 9.609913 s