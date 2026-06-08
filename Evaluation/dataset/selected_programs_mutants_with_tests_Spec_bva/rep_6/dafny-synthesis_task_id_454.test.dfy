
method {:test} Test34() {
var r0 := ContainsZ("aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"| && ("aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"[i] == 'z' || "aaaa\U{000F}aaaa\U{0001}aaaaaaaaaaaaa\U{0005}\U{0007}\taaaaaaaaaaaaz\U{000B}\r\U{0003}"[i] == 'Z');
}
method {:test} Test35() {
var r0 := ContainsZ("aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}");
expect r0 <==> exists i :: 0 <= i < |"aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"| && ("aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"[i] == 'z' || "aaa\U{0017}aaaaaaa\U{0003}aaaaaaa\U{0005}aaa\r\U{000F}aaaaaaaaaaaaaZ\U{0011}\U{0013}\ta\U{0007}aa\U{0001}\U{000B}\U{0015}"[i] == 'Z');
}
method {:test} Test36() {
var r0 := ContainsZ("\U{0002}\0\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0\U{0004}"| && ("\U{0002}\0\U{0004}"[i] == 'z' || "\U{0002}\0\U{0004}"[i] == 'Z');
}

// REPEAT 6 - TIME: 21.1413126 s