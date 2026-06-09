
method {:test} Test3() {
var r0 := ContainsZ("\0a");
expect r0 <==> exists i :: 0 <= i < |"\0a"| && ("\0a"[i] == 'z' || "\0a"[i] == 'Z');
}
method {:test} Test4() {
var r0 := ContainsZ("\U{0003}\U{0001}Z");
expect r0 <==> exists i :: 0 <= i < |"\U{0003}\U{0001}Z"| && ("\U{0003}\U{0001}Z"[i] == 'z' || "\U{0003}\U{0001}Z"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("Z\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Z\U{0001}"| && ("Z\U{0001}"[i] == 'z' || "Z\U{0001}"[i] == 'Z');
}

// REPEAT 2 - TIME: 41.8063389 s