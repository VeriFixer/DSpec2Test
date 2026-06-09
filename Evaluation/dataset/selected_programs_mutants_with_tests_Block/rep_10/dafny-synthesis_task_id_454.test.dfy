
method {:test} Test18() {
var r0 := ContainsZ("\0aaZaaa");
expect r0 <==> exists i :: 0 <= i < |"\0aaZaaa"| && ("\0aaZaaa"[i] == 'z' || "\0aaZaaa"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}z"| && ("\U{0001}z"[i] == 'z' || "\U{0001}z"[i] == 'Z');
}

// REPEAT 10 - TIME: 14.4527527 s