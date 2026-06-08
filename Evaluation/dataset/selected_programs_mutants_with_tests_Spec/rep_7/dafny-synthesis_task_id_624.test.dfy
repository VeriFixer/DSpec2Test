
method {:test} Test6() {
var r0 := ToUppercase("\U{000C}aa\\");
expect |r0| == |"\U{000C}aa\\"|;
expect forall i :: 0 <= i < |"\U{000C}aa\\"| ==> if IsLowerCase("\U{000C}aa\\"[i]) then IsLowerUpperPair("\U{000C}aa\\"[i], r0[i]) else r0[i] == "\U{000C}aa\\"[i];
}

// REPEAT 7 - TIME: 9.9276404 s