method {:testEntry} ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result <==> (exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z'))
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
    }
}

method {:test} Test0() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaZ");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaZ"| && ("aaaaaaaaaaaaaaaaaaaZ"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaZ"[i] == 'Z');
}
method {:test} Test1() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaz"| && ("aaaaaaaaaaaaaaaaaaaz"[i] == 'z' || "aaaaaaaaaaaaaaaaaaaz"[i] == 'Z');
}

// REPEAT 1 - TIME: 2.8441581 s

method {:test} Test2() {
var r0 := ContainsZ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| && ("aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'z' || "aaaaaaaaaaaaaaaaaZaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i] == 'Z');
}
method {:test} Test3() {
var r0 := ContainsZ("aaaaaz");
expect r0 <==> exists i :: 0 <= i < |"aaaaaz"| && ("aaaaaz"[i] == 'z' || "aaaaaz"[i] == 'Z');
}

// REPEAT 2 - TIME: 4.169998 s

method {:test} Test4() {
var r0 := ContainsZ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa");
expect r0 <==> exists i :: 0 <= i < |"Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"| && ("Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'z' || "Zaa\U{0006}aaa\0aaaaaaaaaaaa\U{0002}\U{0004}aa"[i] == 'Z');
}
method {:test} Test5() {
var r0 := ContainsZ("az\U{0001}aa");
expect r0 <==> exists i :: 0 <= i < |"az\U{0001}aa"| && ("az\U{0001}aa"[i] == 'z' || "az\U{0001}aa"[i] == 'Z');
}

// REPEAT 3 - TIME: 5.5132329 s

method {:test} Test6() {
var r0 := ContainsZ("\U{0001}aZaaaaaaaaaaaaa\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}aZaaaaaaaaaaaaa\U{0003}"| && ("\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'z' || "\U{0001}aZaaaaaaaaaaaaa\U{0003}"[i] == 'Z');
}
method {:test} Test7() {
var r0 := ContainsZ("\U{0001}za\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}za\U{0003}"| && ("\U{0001}za\U{0003}"[i] == 'z' || "\U{0001}za\U{0003}"[i] == 'Z');
}

// REPEAT 4 - TIME: 6.9118352 s

method {:test} Test8() {
var r0 := ContainsZ("\0Z");
expect r0 <==> exists i :: 0 <= i < |"\0Z"| && ("\0Z"[i] == 'z' || "\0Z"[i] == 'Z');
}
method {:test} Test9() {
var r0 := ContainsZ("zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa");
expect r0 <==> exists i :: 0 <= i < |"zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"| && ("zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"[i] == 'z' || "zaaaa\U{0002}aaaaa\0aaa\U{0004}aaa"[i] == 'Z');
}

// REPEAT 5 - TIME: 8.3151431 s

method {:test} Test10() {
var r0 := ContainsZ("Z");
expect r0 <==> exists i :: 0 <= i < |"Z"| && ("Z"[i] == 'z' || "Z"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("\0\U{0002}z");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}z"| && ("\0\U{0002}z"[i] == 'z' || "\0\U{0002}z"[i] == 'Z');
}

// REPEAT 6 - TIME: 9.665623 s

method {:test} Test12() {
var r0 := ContainsZ("\U{0004}a\0Za\U{0002}aaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\0Za\U{0002}aaaaaa"| && ("\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'z' || "\U{0004}a\0Za\U{0002}aaaaaa"[i] == 'Z');
}
method {:test} Test13() {
var r0 := ContainsZ("\0\U{0002}za\U{0004}");
expect r0 <==> exists i :: 0 <= i < |"\0\U{0002}za\U{0004}"| && ("\0\U{0002}za\U{0004}"[i] == 'z' || "\0\U{0002}za\U{0004}"[i] == 'Z');
}

// REPEAT 7 - TIME: 10.8190818 s

method {:test} Test14() {
var r0 := ContainsZ("aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}");
expect r0 <==> exists i :: 0 <= i < |"aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"| && ("aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"[i] == 'z' || "aaaaa\U{0004}aaaaa\U{0008}aaaaa\na\U{000C}\U{000E}aaa\U{0012}\U{0010}aa\0aaaaaaaaaZa\U{0006}aa\U{0002}aaaaa\U{0014}"[i] == 'Z');
}
method {:test} Test15() {
var r0 := ContainsZ("\U{0002}\0z");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}\0z"| && ("\U{0002}\0z"[i] == 'z' || "\U{0002}\0z"[i] == 'Z');
}

// REPEAT 8 - TIME: 12.1623788 s

method {:test} Test16() {
var r0 := ContainsZ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"| && ("Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'z' || "Zaaaa\U{0006}aaaa\U{0004}aaaaaaaa\U{0008}aaaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaa"[i] == 'Z');
}
method {:test} Test17() {
var r0 := ContainsZ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa");
expect r0 <==> exists i :: 0 <= i < |"\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"| && ("\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'z' || "\U{0002}z\U{0004}aaaaaaaaaa\0aaaaaaa"[i] == 'Z');
}

// REPEAT 9 - TIME: 13.3181717 s

method {:test} Test18() {
var r0 := ContainsZ("\0aaZaaa");
expect r0 <==> exists i :: 0 <= i < |"\0aaZaaa"| && ("\0aaZaaa"[i] == 'z' || "\0aaZaaa"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("\U{0001}z");
expect r0 <==> exists i :: 0 <= i < |"\U{0001}z"| && ("\U{0001}z"[i] == 'z' || "\U{0001}z"[i] == 'Z');
}

// REPEAT 10 - TIME: 14.4527527 s
