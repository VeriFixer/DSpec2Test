
method {:test} Test4() {
var r0 := ContainsZ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa");
expect r0 <==> exists i :: 0 <= i < |"Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"| && ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'z' || "Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("az\U{0001}aa");
expect r0 <==> exists i :: 0 <= i < |"az\U{0001}aa"| && ("az\U{0001}aa"[i] == 'z' || "az\U{0001}aa"[i] == 'Z');
}

// REPEAT 3 - TIME: 5.6147118 s