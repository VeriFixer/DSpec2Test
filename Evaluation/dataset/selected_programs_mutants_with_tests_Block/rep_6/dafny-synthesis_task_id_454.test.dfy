
method {:test} Test10() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\0\U{0002}z");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}z"| && ("\0\U{0002}z"[i] == 'z' || "\0\U{0002}z"[i] == 'Z');
}

// REPEAT 6 - TIME: 9.665623 s