
method {:test} Test27() {
var r0 := ContainsZ("\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}");
expect r0 <==> exists i :: 0 <= i < |"\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"| && ("\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[i] == 'z' || "\n\U{0008}\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0002}"[i] == 'Z');
}
method {:test} Test28() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}

// REPEAT 10 - TIME: 723.6160778 s