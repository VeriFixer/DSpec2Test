
method {:test} Test28() {
var r0 := ContainsZ("\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"| && ("\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"[i] == 'z' || "\U{0005}aaaaaaaa\U{0001}a\U{0003}aaaaaaaaa\U{0007}a\raaaaaaaaaaaaaaz\U{0011}\U{0013}a\ta\U{000B}aa\U{000F}\U{0015}"[i] == 'Z');
}
method {:test} Test29() {
var r0 := ContainsZ("\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"| && ("\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"[i] == 'z' || "\U{0007}\U{0003}aaaaaaaaaaaaaaaaaaa\U{0005}aaa\U{0001}aaaaaaaaaaaaZaa"[i] == 'Z');
}
method {:test} Test30() {
var r0 := ContainsZ("\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}");
expect r0 <==> exists i :: 0 <= i < |"\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"| && ("\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"[i] == 'z' || "\U{0008}aa\naaaaaa\U{0002}aaaa\0aaaaa\U{0004}a\U{0006}"[i] == 'Z');
}

// REPEAT 4 - TIME: 15.7008722 s