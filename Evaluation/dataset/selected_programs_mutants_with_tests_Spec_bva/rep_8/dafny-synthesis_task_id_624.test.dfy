
method {:test} Test16() {
var r0 := ToUppercase("\U{001C}\U{000C}8a");
expect |r0| == |"\U{001C}\U{000C}8a"|;
expect forall i :: 0 <= i < |"\U{001C}\U{000C}8a"| ==> if IsLowerCase("\U{001C}\U{000C}8a"[i]) then IsLowerUpperPair("\U{001C}\U{000C}8a"[i], r0[i]) else r0[i] == "\U{001C}\U{000C}8a"[i];
}

// REPEAT 8 - TIME: 13.7974755 s