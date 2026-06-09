
method {:test} Test22() {
var r0 := ContainsZ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"| && ("a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'z' || "a\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaz\U{0005}aaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test23() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test24() {
var r0 := ContainsZ("\U{0004}\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}\0\U{0002}"| && ("\U{0004}\0\U{0002}"[i] == 'z' || "\U{0004}\0\U{0002}"[i] == 'Z');
}

// REPEAT 2 - TIME: 12.9319159 s