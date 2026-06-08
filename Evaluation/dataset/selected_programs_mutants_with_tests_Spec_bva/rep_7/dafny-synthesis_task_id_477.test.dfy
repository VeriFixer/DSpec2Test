
method {:test} Test15() {
var r0 := ToLowercase("-\U{0010}aaaa\U{000F}a  ");
expect |r0| == |"-\U{0010}aaaa\U{000F}a  "|;
expect forall i :: 0 <= i < |"-\U{0010}aaaa\U{000F}a  "| ==> if IsUpperCase("-\U{0010}aaaa\U{000F}a  "[i]) then IsUpperLowerPair("-\U{0010}aaaa\U{000F}a  "[i], r0[i]) else r0[i] == "-\U{0010}aaaa\U{000F}a  "[i];
}

// REPEAT 7 - TIME: 12.8318222 s