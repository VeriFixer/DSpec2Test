
method {:test} Test16() {
var r0 := RemoveChars("\U{0004}aa\U{0004}", "\U{0002}\U{0004}\0");
expect |r0| <= |"\U{0004}aa\U{0004}"|;
expect forall i :: 0 <= i < |r0| ==> r0[i] in "\U{0004}aa\U{0004}" && !(r0[i] in "\U{0002}\U{0004}\0");
expect forall i :: 0 <= i < |"\U{0004}aa\U{0004}"| ==> "\U{0004}aa\U{0004}"[i] in "\U{0002}\U{0004}\0" || "\U{0004}aa\U{0004}"[i] in r0;
}

// REPEAT 5 - TIME: 10.7743684 s