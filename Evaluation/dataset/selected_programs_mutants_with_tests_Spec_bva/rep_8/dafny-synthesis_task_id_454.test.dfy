
method {:test} Test40() {
var r0 := ContainsZ("aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"| && ("aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"[i] == 'z' || "aaaaa\U{0013}aaaaaaaaaaaaaaaaaa\t\U{000B}aaaa\U{0007}aaaaa\U{0005}aza\r\U{000F}aaaa\U{0003}a\U{0011}\U{0001}"[i] == 'Z');
}
method {:test} Test41() {
var r0 := ContainsZ("\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa");
expect r0 <==> exists i :: 0 <= i < |"\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"| && ("\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"[i] == 'z' || "\taaaaaaaa\U{0001}aaaaaaaaaaaaaa\U{0003}aaaaaaaaaaaaaZ\U{0005}aa\U{0007}aaaaa"[i] == 'Z');
}
method {:test} Test42() {
var r0 := ContainsZ("\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}");
expect r0 <==> exists i :: 0 <= i < |"\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"| && ("\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"[i] == 'z' || "\naaaaaaaaaaaaaaa\U{0002}aaa\0aaa\U{0006}\U{0004}\U{0008}"[i] == 'Z');
}

// REPEAT 8 - TIME: 22.9846964 s